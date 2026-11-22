import Kernel.Hw

/-! # QEMU `fw_cfg` + `ramfb` Display Driver (`Kernel.Qemu.Ramfb`)

Configures QEMU's `-device ramfb` linear framebuffer via the `fw_cfg` MMIO DMA interface
(`0x09020000` on `-M virt`), allocating a `540 × 1200` `DRM_FORMAT_XRGB8888` scanout buffer in
our capability-checked DMA arena and registering it with `Hw.fbSet`. -/

namespace Kernel.Qemu.Ramfb

def fwCfgDefaultBase : UInt64 := 0x09020000
def regDma : UInt64 := 0x010 -- 64-bit big-endian DMA descriptor physical address

def selFileDir : UInt32 := 0x0019
def dmaCtlError : UInt32 := 0x01
def dmaCtlRead : UInt32 := 0x02
def dmaCtlSelect : UInt32 := 0x08
def dmaCtlWrite : UInt32 := 0x10

/-- `DRM_FORMAT_XRGB8888` = `'X' | ('R'<<8) | ('2'<<16) | ('4'<<24)` = `0x34325258`. -/
def fourccXrgb8888 : UInt32 := 0x34325258

private def bswap32 (v : UInt32) : UInt32 :=
  ((v &&& 0x000000FF) <<< 24) |||
  ((v &&& 0x0000FF00) <<< 8)  |||
  ((v &&& 0x00FF0000) >>> 8)  |||
  ((v &&& 0xFF000000) >>> 24)

private def bswap64 (v : UInt64) : UInt64 :=
  let lo := bswap32 v.toUInt32
  let hi := bswap32 (v >>> 32).toUInt32
  (lo.toUInt64 <<< 32) ||| hi.toUInt64

private def pushBe32 (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push ((v >>> 24) &&& 0xff).toUInt8
   |>.push ((v >>> 16) &&& 0xff).toUInt8
   |>.push ((v >>> 8) &&& 0xff).toUInt8
   |>.push (v &&& 0xff).toUInt8

private def pushBe64 (b : ByteArray) (v : UInt64) : ByteArray :=
  pushBe32 (pushBe32 b (v >>> 32).toUInt32) v.toUInt32

private def readBe16 (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 2 ≤ b.size then
    ((b.get! off).toUInt32 <<< 8) ||| (b.get! (off + 1)).toUInt32
  else 0

private def readBe32 (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 4 ≤ b.size then
    ((b.get! off).toUInt32 <<< 24) |||
    ((b.get! (off + 1)).toUInt32 <<< 16) |||
    ((b.get! (off + 2)).toUInt32 <<< 8) |||
    (b.get! (off + 3)).toUInt32
  else 0

private def readCStrAt (b : ByteArray) (off maxLen : Nat) : String := Id.run do
  let mut out : Array UInt8 := #[]
  let lim := min b.size (off + maxLen)
  for i in [off:lim] do
    let c := b.get! i
    if c == 0 then break
    out := out.push c
  return String.fromUTF8! (ByteArray.mk out)

/-- Issues one synchronous `fw_cfg` DMA operation via `descAddr` (16 bytes in DMA arena). -/
private def dmaTransfer (fwBase descAddr : UInt64) (control length : UInt32) (bufAddr : UInt64) : BaseIO Bool := do
  let pkt := pushBe64 (pushBe32 (pushBe32 ByteArray.empty control) length) bufAddr
  Hw.store descAddr pkt
  -- Write big-endian 64-bit descriptor physical address to `fwBase + 0x10` (triggers DMA immediately).
  Hw.write64 (fwBase + regDma) (bswap64 descAddr)
  for _ in [0:100000] do
    let st ← Hw.load descAddr 4
    let ctl := readBe32 st 0
    if ctl == 0 then return true
    if (ctl &&& dmaCtlError) != 0 then return false
    Hw.pause
  return false

/-- Discovers `etc/ramfb` in `fw_cfg` and configures a `w × h` `XRGB8888` scanout framebuffer. -/
def init (fwBase : UInt64 := fwCfgDefaultBase) (w h : UInt32 := 540) : BaseIO (Option UInt64) := do
  -- Verify `fwBase` is an announced MMIO window before touching it.
  let wins ← Hw.windows
  if !wins.any (fun win => win.base ≤ fwBase && fwBase + 0x18 ≤ win.base + win.size) then
    return none
  let descAddr ← Hw.alloc 64
  let dirBuf ← Hw.alloc 8192
  if descAddr == 0 || dirBuf == 0 then return none
  -- 1. Read file directory count (4 bytes)
  let selCtl := (selFileDir <<< 16) ||| dmaCtlSelect ||| dmaCtlRead
  if !(← dmaTransfer fwBase descAddr selCtl 4 dirBuf) then return none
  let cntBytes ← Hw.load dirBuf 4
  let count := min (readBe32 cntBytes 0).toNat 120
  if count == 0 then return none
  -- 2. Read `count` × 64-byte `FWCfgFile` entries
  let entriesBytes := count * 64
  if !(← dmaTransfer fwBase descAddr dmaCtlRead entriesBytes.toUInt32 dirBuf) then return none
  let entries ← Hw.load dirBuf entriesBytes.toUSize
  let mut ramfbSel? : Option UInt32 := none
  for i in [0:count] do
    let off := i * 64
    let sel := readBe16 entries (off + 4)
    let name := readCStrAt entries (off + 8) 56
    if name == "etc/ramfb" then
      ramfbSel? := some sel
  let some ramfbSel := ramfbSel? | return none
  -- 3. Allocate scanout framebuffer in DMA arena (aligned to 4 KiB)
  let fbBytes : Nat := w.toNat * h.toNat * 4
  let fbAddr ← Hw.alloc fbBytes.toUSize
  if fbAddr == 0 then return none
  -- 4. Write 28-byte big-endian `RAMFBCfg` to `etc/ramfb`
  let stride := w * 4
  let cfg := pushBe32 (pushBe32 (pushBe32 (pushBe32 (pushBe32 (pushBe64 ByteArray.empty fbAddr)
    fourccXrgb8888) 0) w) h) stride
  Hw.store dirBuf cfg
  let wrCtl := (ramfbSel <<< 16) ||| dmaCtlSelect ||| dmaCtlWrite
  if !(← dmaTransfer fwBase descAddr wrCtl 28 dirBuf) then return none
  Hw.fbSet fbAddr w h w
  return some fbAddr

end Kernel.Qemu.Ramfb
