/-! # Verified Zero-Filesystem Wire Framing Protocol (`Kernel.Wire`)

Length-prefixed request/response frame protocol shared identically across:
- QEMU bare-metal PL011 UART (`Kernel/Qemu/Pl011.lean`)
- Pixel 9 Pro XL polled USB-C DWC3 raw bulk (`Kernel/Komodo/Dwc3.lean`)
- Host CLI (`tools/tricorder_usb.c`)

Wire Format (all multi-byte integers little-endian):
- `[0..4)`       Magic `"TRIW"` (`0x54, 0x52, 0x49, 0x57`)
- `[4]`          `op : UInt8`
- `[5]`          `flags : UInt8`
- `[6..8)`       `len : UInt16` (`≤ maxPayload = 16384`)
- `[8..8+len)`   `payload`
- `[8+len..12+len)` `crc32 : UInt32` (IEEE 802.3 CRC-32 over `[0..8+len)`)

Notice: the host NEVER gets a direct "sign now" command — `pushOverride`
only loads a PSBT onto the Pixel's OLED screen for human review; actual signing ALWAYS requires
physical two-step arm + confirm on the device's buttons.

Formal round-trip, bounds, and locked-state gating proofs live in `Kernel/WireProofs.lean`. -/

namespace Kernel.Wire

def magic : ByteArray := "TRIW".toUTF8
def headerSize : Nat := 8
def trailerSize : Nat := 4
def maxPayload : Nat := 16384

/-- Wire operation codes. -/
inductive Op where
  | ping           -- 0x01: liveness + network name
  | getStatus      -- 0x02: current screen, unlocked?, hasWallet?, armed?
  | getKeys        -- 0x03: export override xpub (requires unlocked)
  | pushDescriptor -- 0x04: load wallet descriptor onto OLED for user verification (requires unlocked)
  | pushOverride   -- 0x05: load Override PSBT onto OLED for review (requires unlocked + wallet)
  | pollResult     -- 0x07: read the last signed PSBT, if its holder signed (requires unlocked)
  | injectKey      -- 0x10: a key event from the host (0=prev,1=next,2=select,3=back); regtest builds only
  | lab            -- 0x20: hardware bring-up: read and write device registers from the host; regtest builds only
  | respOk         -- 0x80: success reply payload
  | respErr        -- 0x81: UTF-8 error message
  deriving BEq, DecidableEq, Repr, Inhabited

def Op.toByte : Op → UInt8
  | .ping           => 0x01
  | .getStatus      => 0x02
  | .getKeys        => 0x03
  | .pushDescriptor => 0x04
  | .pushOverride   => 0x05
  | .pollResult     => 0x07
  | .injectKey      => 0x10
  | .lab            => 0x20
  | .respOk         => 0x80
  | .respErr        => 0x81

def Op.ofByte? : UInt8 → Option Op
  | 0x01 => some .ping
  | 0x02 => some .getStatus
  | 0x03 => some .getKeys
  | 0x04 => some .pushDescriptor
  | 0x05 => some .pushOverride
  | 0x07 => some .pollResult
  | 0x10 => some .injectKey
  | 0x20 => some .lab
  | 0x80 => some .respOk
  | 0x81 => some .respErr
  | _    => none

/-- Whether an operation requires the vault to be unlocked on the device. -/
def Op.requiresUnlocked : Op → Bool
  | .getKeys | .pushDescriptor | .pushOverride | .pollResult => true
  | _ => false

/-- Whether an operation puts something new on the screen for its holder to review. -/
def Op.isPush : Op → Bool
  | .pushDescriptor | .pushOverride => true
  | _ => false

/-- Operations that exist for tests and for bringing hardware up, and are refused outside a regtest build:
the host pressing the buttons, and the host reading and writing device registers. -/
def Op.isTestOnly : Op → Bool
  | .injectKey | .lab => true
  | _ => false

/-- Whether an operation is allowed in the current security state.

- `unlocked`: the vault is open.
- `reviewing`: a wallet or a payment is on the screen, waiting for its holder's answer. Nothing may replace
  it from the cable: what is read is what is signed. Its holder answers on the device first.
- `testBuild`: the image was built for a test chain with no value (regtest). Only there may the host press
  the buttons, which the tests under emulation need; on signet and mainnet a person presses them. -/
def Op.allowed (op : Op) (unlocked : Bool) (reviewing : Bool) (testBuild : Bool) : Bool :=
  if op.requiresUnlocked && !unlocked then false
  else if op.isPush && reviewing then false
  else if op.isTestOnly && !testBuild then false
  else true

structure Frame where
  op : Op
  flags : UInt8 := 0
  payload : ByteArray := ByteArray.empty
  deriving BEq, Inhabited

/-- Standard IEEE 802.3 CRC-32 (polynomial `0xEDB88320`). -/
def crc32 (b : ByteArray) : UInt32 := Id.run do
  let mut c : UInt32 := 0xFFFFFFFF
  for i in [0:b.size] do
    c := c ^^^ (b.get! i).toUInt32
    for _ in [0:8] do
      if (c &&& 1) != 0 then
        c := (c >>> 1) ^^^ 0xEDB88320
      else
        c := c >>> 1
  return c ^^^ 0xFFFFFFFF

private def pushU16Le (b : ByteArray) (v : Nat) : ByteArray :=
  b.push (v &&& 0xff).toUInt8 |>.push ((v >>> 8) &&& 0xff).toUInt8

private def pushU32Le (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push (v &&& 0xff).toUInt8
   |>.push ((v >>> 8) &&& 0xff).toUInt8
   |>.push ((v >>> 16) &&& 0xff).toUInt8
   |>.push ((v >>> 24) &&& 0xff).toUInt8

def readU16Le (b : ByteArray) (off : Nat) : Nat :=
  if off + 2 ≤ b.size then
    (b.get! off).toNat ||| ((b.get! (off + 1)).toNat <<< 8)
  else 0

def readU32Le (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 4 ≤ b.size then
    (b.get! off).toUInt32 |||
    ((b.get! (off + 1)).toUInt32 <<< 8) |||
    ((b.get! (off + 2)).toUInt32 <<< 16) |||
    ((b.get! (off + 3)).toUInt32 <<< 24)
  else 0

/-- Encodes a `Frame` into raw wire bytes. Truncates only if payload exceeds `maxPayload`. -/
def encode (f : Frame) : ByteArray :=
  let payload := if f.payload.size ≤ maxPayload then f.payload else f.payload.extract 0 maxPayload
  let hdr := pushU16Le ((magic.push f.op.toByte).push f.flags) payload.size
  let body := hdr ++ payload
  pushU32Le body (crc32 body)

/-- Decodes and CRC-32-verifies a complete raw wire frame. -/
def decode (raw : ByteArray) : Except String Frame :=
  if raw.size < headerSize + trailerSize then .error "frame too short"
  else if raw.extract 0 4 != magic then .error "bad wire magic"
  else match Op.ofByte? (raw.get! 4) with
    | none => .error "unknown wire op"
    | some op =>
      let flags := raw.get! 5
      let len := readU16Le raw 6
      if len > maxPayload then .error "wire payload exceeds maxPayload"
      else if raw.size != headerSize + len + trailerSize then .error "wire length mismatch"
      else
        let body := raw.extract 0 (headerSize + len)
        let wantCrc := readU32Le raw (headerSize + len)
        if crc32 body != wantCrc then .error "wire CRC-32 mismatch"
        else .ok { op, flags, payload := raw.extract headerSize (headerSize + len) }

end Kernel.Wire
