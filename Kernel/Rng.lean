import Winnow.Crypto.Sha2
import Kernel.Hw

/-! # Verified Hardware Entropy Collector & Health Checks (`Kernel.Rng`)

Collects entropy from hardware sources (ARMv8.5 `RNDRRS`/`RNDR` via `Hw.rndr`, VirtIO-RNG in
QEMU, or Exynos TRNG on Pixel `komodo`) and runs fail-closed NIST SP 800-90B style health checks
before conditioning via SHA-256:

- Rejects any 32-byte raw sample that is all-`0x00`, all-`0xFF`, or repeats the same 64-bit word
  across all 4 words (catches dead/unclocked/stuck hardware TRNGs!).
- Conditions raw hardware words with SHA-256 + counter before emitting key/nonce bytes.

Formal fail-closed proofs live in `Kernel/RngProofs.lean`. -/

namespace Kernel.Rng

def readLe64 (b : ByteArray) (off : Nat) : UInt64 :=
  if off + 8 ≤ b.size then
    (b.get! off).toUInt64 |||
    ((b.get! (off + 1)).toUInt64 <<< 8) |||
    ((b.get! (off + 2)).toUInt64 <<< 16) |||
    ((b.get! (off + 3)).toUInt64 <<< 24) |||
    ((b.get! (off + 4)).toUInt64 <<< 32) |||
    ((b.get! (off + 5)).toUInt64 <<< 40) |||
    ((b.get! (off + 6)).toUInt64 <<< 48) |||
    ((b.get! (off + 7)).toUInt64 <<< 56)
  else 0

def pushLe64 (b : ByteArray) (v : UInt64) : ByteArray :=
  b.push (v &&& 0xff).toUInt8
   |>.push ((v >>> 8) &&& 0xff).toUInt8
   |>.push ((v >>> 16) &&& 0xff).toUInt8
   |>.push ((v >>> 24) &&& 0xff).toUInt8
   |>.push ((v >>> 32) &&& 0xff).toUInt8
   |>.push ((v >>> 40) &&& 0xff).toUInt8
   |>.push ((v >>> 48) &&& 0xff).toUInt8
   |>.push ((v >>> 56) &&& 0xff).toUInt8

/-- Fail-closed health check on 4 raw 64-bit hardware entropy words (`w0..w3`):
rejects all-zero, all-ones, or any adjacent identical 64-bit words (stuck/repeating TRNG). -/
def wordsHealthy (w0 w1 w2 w3 : UInt64) : Bool :=
  let allZero := (w0 == 0) && (w1 == 0) && (w2 == 0) && (w3 == 0)
  let allOnes := (w0 == 0xFFFFFFFFFFFFFFFF) && (w1 == 0xFFFFFFFFFFFFFFFF) &&
                 (w2 == 0xFFFFFFFFFFFFFFFF) && (w3 == 0xFFFFFFFFFFFFFFFF)
  let stuck := (w0 == w1) || (w1 == w2) || (w2 == w3) || (w0 == w2) || (w0 == w3) || (w1 == w3)
  !(allZero || allOnes || stuck)

/-- Conditions 4 verified 64-bit hardware entropy words into 32 uniform bytes via SHA-256. -/
def conditionBlock (w0 w1 w2 w3 : UInt64) (domainCtr : UInt64) : Except String ByteArray :=
  if !wordsHealthy w0 w1 w2 w3 then
    .error "hardware RNG failed health check (degenerate or repeating words)"
  else
    let raw := pushLe64 (pushLe64 (pushLe64 (pushLe64 (pushLe64 "TRICORDER-RNG-V1".toUTF8 domainCtr) w0) w1) w2) w3
    .ok (Winnow.sha256 raw)

/-- Reads one hardware 64-bit word via `Hw.rndr` with bounded retry (never spins forever). -/
def readRndrRetry (attempts : Nat := 32) : BaseIO (Option UInt64) := do
  for _ in [0:attempts] do
    match ← Hw.rndr with
    | some w => return some w
    | none => Hw.pause
  return none

/-- Collects `count` health-checked, SHA-256-conditioned hardware random bytes from a 64-bit word source. -/
def collectFrom (nextWord : BaseIO (Option UInt64)) (count : Nat) : BaseIO (Except String ByteArray) := do
  let mut out := ByteArray.empty
  let mut ctr : UInt64 := 0
  while out.size < count do
    let some w0 ← nextWord | return .error "hardware RNG returned no entropy (w0)"
    let some w1 ← nextWord | return .error "hardware RNG returned no entropy (w1)"
    let some w2 ← nextWord | return .error "hardware RNG returned no entropy (w2)"
    let some w3 ← nextWord | return .error "hardware RNG returned no entropy (w3)"
    match conditionBlock w0 w1 w2 w3 ctr with
    | .error e => return .error e
    | .ok blk =>
      let need := count - out.size
      out := out ++ (if blk.size ≤ need then blk else blk.extract 0 need)
      ctr := ctr + 1
  return .ok out

/-- Collects `count` bytes directly from AArch64 `RNDRRS`/`RNDR`. -/
def collectRndr (count : Nat) : BaseIO (Except String ByteArray) :=
  collectFrom (readRndrRetry 32) count

end Kernel.Rng
