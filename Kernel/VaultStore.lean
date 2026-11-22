import Winnow.Crypto.Sha2

/-! # Zero-Filesystem 2-Slot Raw Block Vault Persistence (`Kernel.VaultStore`)

Replaces all filesystems (F2FS/ext4/FAT) with **two 4096-byte raw UFS/virtio-blk blocks**:
- Slot 0 (`LBA 0`) and Slot 1 (`LBA 1`).
- Every write targets the **inactive** slot with `seq := prevSeq + 1`, so a power cut or torn write
  mid-sector NEVER destroys the last committed vault.
- Each 4096-byte slot ends with `SHA-256(bytes[0..4064))`; wipe overwrites BOTH slots with `0x00`.

Slot Layout (4096 bytes):
- `[0..8)`      Magic `"TRIVLT01"`
- `[8..16)`     `seq : UInt64` (LE, ≥ 1 for active slots)
- `[16..20)`    `failedAttempts : UInt32` (LE)
- `[20..24)`    `vaultLen : UInt32` (LE, ≤ 1024)
- `[24..28)`    `descLen : UInt32` (LE, ≤ 2048)
- `[28..32)`    `flags : UInt32` (bit 0 = `hasVault`)
- `[32..1056)`  Encrypted `vault.bin` bytes (zero-padded)
- `[1056..3104)` Registered wallet descriptor UTF-8 bytes (zero-padded)
- `[3104..4064)` Reserved zeros
- `[4064..4096)` `SHA-256(slot[0..4064))`

All crash-consistency, monotonic-commit, and wipe invariants are formally proved in
`Kernel/VaultStoreProofs.lean`. -/

namespace Kernel.VaultStore

def slotBytes : Nat := 4096
def payloadEnd : Nat := 4064
def maxVaultLen : Nat := 1024
def maxDescLen : Nat := 2048
def vaultOffset : Nat := 32
def descOffset : Nat := 1056
def slotMagic : ByteArray := "TRIVLT01".toUTF8

def zeroSlot : ByteArray := ByteArray.mk (Array.replicate slotBytes 0)

/-- Logical state persisted in one 4 KiB raw flash slot. -/
structure SlotRecord where
  seq : Nat
  failedAttempts : Nat
  vault? : Option ByteArray
  descriptor? : Option ByteArray
  deriving BEq, Inhabited

def SlotRecord.wellFormed (r : SlotRecord) : Bool :=
  r.seq ≥ 1 &&
  r.seq < 2 ^ 64 &&
  r.failedAttempts < 2 ^ 32 &&
  (match r.vault? with | none => true | some v => v.size ≤ maxVaultLen) &&
  (match r.descriptor? with | none => true | some d => d.size ≤ maxDescLen)

private def putU32LeAt (a : Array UInt8) (off : Nat) (v : Nat) : Array UInt8 :=
  a.set! off (v &&& 0xff).toUInt8
   |>.set! (off + 1) ((v >>> 8) &&& 0xff).toUInt8
   |>.set! (off + 2) ((v >>> 16) &&& 0xff).toUInt8
   |>.set! (off + 3) ((v >>> 24) &&& 0xff).toUInt8

private def putU64LeAt (a : Array UInt8) (off : Nat) (v : Nat) : Array UInt8 :=
  let a := putU32LeAt a off (v &&& 0xffffffff)
  putU32LeAt a (off + 4) ((v >>> 32) &&& 0xffffffff)

def readU32Le (b : ByteArray) (off : Nat) : Nat :=
  if off + 4 ≤ b.size then
    (b.get! off).toNat |||
    ((b.get! (off + 1)).toNat <<< 8) |||
    ((b.get! (off + 2)).toNat <<< 16) |||
    ((b.get! (off + 3)).toNat <<< 24)
  else 0

def readU64Le (b : ByteArray) (off : Nat) : Nat :=
  readU32Le b off ||| (readU32Le b (off + 4) <<< 32)

private def copyInto (dst : Array UInt8) (off : Nat) (src : ByteArray) : Array UInt8 := Id.run do
  let mut out := dst
  let lim := min src.size (out.size - off)
  for i in [0:lim] do
    out := out.set! (off + i) (src.get! i)
  return out

/-- Encodes a `SlotRecord` into a self-authenticating 4096-byte raw block. -/
def encodeSlot (r : SlotRecord) : ByteArray :=
  let a := Array.replicate slotBytes (0 : UInt8)
  let a := copyInto a 0 slotMagic
  let a := putU64LeAt a 8 r.seq
  let a := putU32LeAt a 16 r.failedAttempts
  let (flags, vLen, a) := match r.vault? with
    | none => (0, 0, a)
    | some v =>
      let n := min v.size maxVaultLen
      (1, n, copyInto a vaultOffset (v.extract 0 n))
  let (flags, dLen, a) := match r.descriptor? with
    | none => (flags, 0, a)
    | some d =>
      let n := min d.size maxDescLen
      (flags ||| 2, n, copyInto a descOffset (d.extract 0 n))
  let a := putU32LeAt a 20 vLen
  let a := putU32LeAt a 24 dLen
  let a := putU32LeAt a 28 flags
  let body := ByteArray.mk (a.extract 0 payloadEnd)
  let tag := Winnow.sha256 body
  ByteArray.mk (copyInto a payloadEnd tag)

/-- Decodes and authenticates a 4096-byte raw slot block. Returns `none` on empty/corrupt blocks. -/
def decodeSlot (raw : ByteArray) : Option SlotRecord :=
  if raw.size != slotBytes then none
  else if raw.get! 0 != 0x54 then none
  else if raw.extract 0 8 != slotMagic then none
  else
    let body := raw.extract 0 payloadEnd
    let storedTag := raw.extract payloadEnd slotBytes
    if Winnow.sha256 body != storedTag then none
    else
      let seq := readU64Le raw 8
      if seq == 0 then none
      else
        let failedAttempts := readU32Le raw 16
        let vLen := readU32Le raw 20
        let dLen := readU32Le raw 24
        let flags := readU32Le raw 28
        if vLen > maxVaultLen || dLen > maxDescLen then none
        else
          let vault? := if (flags &&& 1) != 0 then some (raw.extract vaultOffset (vaultOffset + vLen)) else none
          let descriptor? := if (flags &&& 2) != 0 then some (raw.extract descOffset (descOffset + dLen)) else none
          some { seq, failedAttempts, vault?, descriptor? }

/-- Index of the two raw flash slots (`false` = Slot 0, `true` = Slot 1). -/
abbrev SlotIdx := Bool

/-- The two-slot raw flash block device image `(slot0, slot1)`. -/
structure DualDisk where
  slot0 : ByteArray
  slot1 : ByteArray
  deriving BEq

def DualDisk.get (d : DualDisk) : SlotIdx → ByteArray
  | false => d.slot0
  | true  => d.slot1

def DualDisk.set (d : DualDisk) (idx : SlotIdx) (blk : ByteArray) : DualDisk :=
  match idx with
  | false => { d with slot0 := blk }
  | true  => { d with slot1 := blk }

/-- Recovers the newest valid `(activeSlotIdx, record)` from the two raw blocks, or `none` if blank/wiped. -/
def recover (d : DualDisk) : Option (SlotIdx × SlotRecord) :=
  match decodeSlot d.slot0, decodeSlot d.slot1 with
  | none, none => none
  | some r0, none => some (false, r0)
  | none, some r1 => some (true, r1)
  | some r0, some r1 =>
    if r1.seq > r0.seq then some (true, r1) else some (false, r0)

/-- Computes the target slot index and next monotonic `seq` for an atomic update.
Always writes to the **inactive** slot (`!activeIdx`) so the active slot is never overwritten in place. -/
def planWrite (d : DualDisk) : SlotIdx × Nat :=
  match recover d with
  | none => (false, 1)
  | some (activeIdx, rec) => (!activeIdx, rec.seq + 1)

/-- Performs a single atomic slot commit onto the inactive slot of `DualDisk`. -/
def commit (d : DualDisk) (failedAttempts : Nat) (vault? desc? : Option ByteArray) : DualDisk :=
  let (targetIdx, nextSeq) := planWrite d
  let blk := encodeSlot { seq := nextSeq, failedAttempts, vault?, descriptor? := desc? }
  d.set targetIdx blk

/-- Overwrites BOTH slots with zeros (used on manual wipe or 10 consecutive wrong PINs). -/
def wipeBoth (_ : DualDisk) : DualDisk :=
  { slot0 := zeroSlot, slot1 := zeroSlot }

end Kernel.VaultStore
