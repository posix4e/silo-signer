import Kernel.Hw

/-! # Polled VirtIO-MMIO v2 Drivers in Lean (`Kernel.Qemu.VirtioMmio`)

Adapted cleanly from `silo-os/Kernel/Virtio.lean` & `Virtq.lean` for QEMU `-M virt` AArch64:
- **`VirtioRng`** (`deviceId = 4`): polls hardware random bytes from QEMU `virtio-rng-device`.
- **`VirtioBlk`** (`deviceId = 2`): polls 4096-byte raw block reads & writes (`8 × 512B` sectors)
  backing our formally verified 2-slot `Kernel.VaultStore` with zero filesystem!

Every register access and DMA buffer transfer goes strictly through `Kernel.Hw` capability checks. -/

namespace Kernel.Qemu.VirtioMmio

def regMagic : UInt64 := 0x000
def regVersion : UInt64 := 0x004
def regDeviceId : UInt64 := 0x008
def regDeviceFeatures : UInt64 := 0x010
def regDeviceFeaturesSel : UInt64 := 0x014
def regDriverFeatures : UInt64 := 0x020
def regDriverFeaturesSel : UInt64 := 0x024
def regQueueSel : UInt64 := 0x030
def regQueueNumMax : UInt64 := 0x034
def regQueueNum : UInt64 := 0x038
def regQueueReady : UInt64 := 0x044
def regQueueNotify : UInt64 := 0x050
def regStatus : UInt64 := 0x070
def regQueueDescLow : UInt64 := 0x080
def regQueueDescHigh : UInt64 := 0x084
def regQueueDriverLow : UInt64 := 0x090
def regQueueDriverHigh : UInt64 := 0x094
def regQueueDeviceLow : UInt64 := 0x0a0
def regQueueDeviceHigh : UInt64 := 0x0a4

def virtioMagic : UInt32 := 0x74726976
def statusAck : UInt32 := 1
def statusDriver : UInt32 := 2
def statusDriverOk : UInt32 := 4
def statusFeaturesOk : UInt32 := 8

def idBlk : UInt32 := 2
def idRng : UInt32 := 4

def descFlagNext : UInt32 := 1
def descFlagWrite : UInt32 := 2

def blkReqIn : UInt32 := 0  -- READ
def blkReqOut : UInt32 := 1 -- WRITE
def blkReqFlush : UInt32 := 4

private def leBytes (v : Nat) (n : Nat) : ByteArray := Id.run do
  let mut b := ByteArray.empty
  for i in [0:n] do
    b := b.push ((v >>> (8 * i)) &&& 0xff).toUInt8
  return b

private def readLe16 (b : ByteArray) (off : Nat) : Nat :=
  if off + 2 ≤ b.size then
    (b.get! off).toNat ||| ((b.get! (off + 1)).toNat <<< 8)
  else 0

private def makeDesc (addr : UInt64) (len : Nat) (flags : UInt32) (next : Nat) : ByteArray :=
  leBytes addr.toNat 8 ++ leBytes len 4 ++ leBytes flags.toNat 2 ++ leBytes next 2

structure Device where
  base : UInt64
  id : UInt32
  deriving Repr, Inhabited

/-- Discovers all VirtIO-MMIO v2 devices across QEMU's announced VirtIO-MMIO windows (`0x0a000000..0x0a004000`). -/
def discover : BaseIO (Array Device) := do
  let mut found : Array Device := #[]
  for w in ← Hw.windows do
    if w.size != 0x200 || w.base < 0x0a000000 || w.base >= 0x0a004000 then continue
    if (← Hw.read32 (w.base + regMagic)) != virtioMagic then continue
    if (← Hw.read32 (w.base + regVersion)) != 2 then continue
    let id ← Hw.read32 (w.base + regDeviceId)
    if id != 0 then found := found.push { base := w.base, id }
  return found

private def negotiate (d : Device) : BaseIO Bool := do
  Hw.write32 (d.base + regStatus) 0
  Hw.write32 (d.base + regStatus) statusAck
  Hw.write32 (d.base + regStatus) (statusAck ||| statusDriver)
  Hw.write32 (d.base + regDeviceFeaturesSel) 1
  let hi ← Hw.read32 (d.base + regDeviceFeatures)
  if (hi &&& 1) == 0 then return false
  Hw.write32 (d.base + regDriverFeaturesSel) 0
  Hw.write32 (d.base + regDriverFeatures) 0
  Hw.write32 (d.base + regDriverFeaturesSel) 1
  Hw.write32 (d.base + regDriverFeatures) 1 -- VIRTIO_F_VERSION_1
  let st := statusAck ||| statusDriver ||| statusFeaturesOk
  Hw.write32 (d.base + regStatus) st
  return ((← Hw.read32 (d.base + regStatus)) &&& statusFeaturesOk) != 0

private def setDriverOk (d : Device) : BaseIO Unit :=
  Hw.write32 (d.base + regStatus) (statusAck ||| statusDriver ||| statusFeaturesOk ||| statusDriverOk)

/-- Fixed 8-entry split virtqueue layout (fits cleanly inside two 4 KiB pages: desc+avail in page 0, used in page 1). -/
structure SplitQueue where
  dev : Device
  qSize : Nat := 8
  descBase : UInt64   -- 8 × 16 = 128 bytes at offset 0
  availBase : UInt64  -- offset 128 (2 + 2 + 8*2 = 20 bytes)
  usedBase : UInt64   -- offset 4096 (page-aligned!)
  availIdx : Nat := 0
  usedIdx : Nat := 0
  deriving Repr, Inhabited

private def setupQueue0 (d : Device) : BaseIO (Option SplitQueue) := do
  Hw.write32 (d.base + regQueueSel) 0
  let maxN := (← Hw.read32 (d.base + regQueueNumMax)).toNat
  if maxN < 4 then return none
  let qSize := min maxN 8
  let mem ← Hw.alloc 8192
  if mem == 0 then return none
  let descBase := mem
  let availBase := mem + 256
  let usedBase := mem + 4096
  Hw.write32 (d.base + regQueueNum) qSize.toUInt32
  Hw.write32 (d.base + regQueueDescLow) descBase.toUInt32
  Hw.write32 (d.base + regQueueDescHigh) (descBase >>> 32).toUInt32
  Hw.write32 (d.base + regQueueDriverLow) availBase.toUInt32
  Hw.write32 (d.base + regQueueDriverHigh) (availBase >>> 32).toUInt32
  Hw.write32 (d.base + regQueueDeviceLow) usedBase.toUInt32
  Hw.write32 (d.base + regQueueDeviceHigh) (usedBase >>> 32).toUInt32
  Hw.write32 (d.base + regQueueReady) 1
  return some { dev := d, qSize, descBase, availBase, usedBase }

private def SplitQueue.submitAndWait (q : SplitQueue) (headDesc : Nat) : BaseIO (Option SplitQueue) := do
  let slot := q.availIdx % q.qSize
  Hw.store (q.availBase + (4 + 2 * slot).toUInt64) (leBytes headDesc 2)
  let nextAvail := (q.availIdx + 1) % 65536
  Hw.store (q.availBase + 2) (leBytes nextAvail 2)
  Hw.write32 (q.dev.base + regQueueNotify) 0
  for _ in [0:4000000] do
    let u ← Hw.load (q.usedBase + 2) 2
    if readLe16 u 0 != q.usedIdx then
      return some { q with availIdx := nextAvail, usedIdx := (q.usedIdx + 1) % 65536 }
    Hw.pause
  return none

/-! ## VirtIO-RNG Driver (`deviceId = 4`) -/

structure VirtioRng where
  q : SplitQueue
  buf : UInt64
  deriving Repr, Inhabited

def VirtioRng.init (devs : Array Device) : BaseIO (Option VirtioRng) := do
  let some d := devs.find? (·.id == idRng) | return none
  if !(← negotiate d) then return none
  let some q ← setupQueue0 d | return none
  let buf ← Hw.alloc 4096
  if buf == 0 then return none
  setDriverOk d
  return some { q, buf }

def VirtioRng.readBytes (r : VirtioRng) (n : Nat) : BaseIO (Option (VirtioRng × ByteArray)) := do
  let len := min n 4096
  Hw.store r.q.descBase (makeDesc r.buf len descFlagWrite 0)
  let some q' ← r.q.submitAndWait 0 | return none
  let bytes ← Hw.load r.buf len.toUSize
  return some ({ r with q := q' }, bytes)

/-! ## VirtIO-BLK Driver (`deviceId = 2`) for Zero-FS 2-Slot `VaultStore` -/

structure VirtioBlk where
  q : SplitQueue
  hdrBuf : UInt64  -- 16-byte virtio_blk_req header
  dataBuf : UInt64 -- 4096-byte raw block buffer
  statBuf : UInt64 -- 1-byte completion status
  deriving Repr, Inhabited

def VirtioBlk.init (devs : Array Device) : BaseIO (Option VirtioBlk) := do
  let some d := devs.find? (·.id == idBlk) | return none
  if !(← negotiate d) then return none
  let some q ← setupQueue0 d | return none
  let hdrBuf ← Hw.alloc 4096
  let dataBuf ← Hw.alloc 4096
  let statBuf ← Hw.alloc 4096
  if hdrBuf == 0 || dataBuf == 0 || statBuf == 0 then return none
  setDriverOk d
  return some { q, hdrBuf, dataBuf, statBuf }

/-- Reads one 4096-byte raw slot (`slotIdx = 0` -> sector 0, `slotIdx = 1` -> sector 8). -/
def VirtioBlk.readBlock4K (b : VirtioBlk) (slotIdx : Nat) : BaseIO (Option (VirtioBlk × ByteArray)) := do
  let sector := slotIdx * 8
  let hdr := leBytes blkReqIn.toNat 4 ++ leBytes 0 4 ++ leBytes sector 8
  Hw.store b.hdrBuf hdr
  Hw.store b.statBuf (ByteArray.mk #[0xFF])
  -- 3-descriptor chain: 0 (hdr, device-read) -> 1 (4KiB data, device-write) -> 2 (1B status, device-write)
  Hw.store (b.q.descBase + 0)  (makeDesc b.hdrBuf 16 descFlagNext 1)
  Hw.store (b.q.descBase + 16) (makeDesc b.dataBuf 4096 (descFlagNext ||| descFlagWrite) 2)
  Hw.store (b.q.descBase + 32) (makeDesc b.statBuf 1 descFlagWrite 0)
  let some q' ← b.q.submitAndWait 0 | return none
  let st ← Hw.load b.statBuf 1
  if st.size == 0 || st.get! 0 != 0 then return none
  let data ← Hw.load b.dataBuf 4096
  return some ({ b with q := q' }, data)

/-- Writes one 4096-byte raw slot (`slotIdx = 0` -> sector 0, `slotIdx = 1` -> sector 8). -/
def VirtioBlk.writeBlock4K (b : VirtioBlk) (slotIdx : Nat) (blk : ByteArray) : BaseIO (Option VirtioBlk) := do
  if blk.size != 4096 then return none
  let sector := slotIdx * 8
  let hdr := leBytes blkReqOut.toNat 4 ++ leBytes 0 4 ++ leBytes sector 8
  Hw.store b.hdrBuf hdr
  Hw.store b.dataBuf blk
  Hw.store b.statBuf (ByteArray.mk #[0xFF])
  Hw.store (b.q.descBase + 0)  (makeDesc b.hdrBuf 16 descFlagNext 1)
  Hw.store (b.q.descBase + 16) (makeDesc b.dataBuf 4096 descFlagNext 2)
  Hw.store (b.q.descBase + 32) (makeDesc b.statBuf 1 descFlagWrite 0)
  let some q' ← b.q.submitAndWait 0 | return none
  let st ← Hw.load b.statBuf 1
  if st.size == 0 || st.get! 0 != 0 then return none
  return some { b with q := q' }

end Kernel.Qemu.VirtioMmio
