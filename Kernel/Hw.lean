import Runtime.Big
import Runtime.Utf8

/-! # Bare-Metal Hardware Capability Interface (`Kernel.Hw`)

Modeled directly on `silo-os/Kernel/Hw.lean`: everything a Lean driver does to silicon passes
through this narrow capability-checked boundary (`rt/bare/hw.c` on AArch64 bare metal,
`rt/hosted/hw.c` for macOS unit tests):

- Device registers (`read32`/`write32`/`read64`/`write64`) may ONLY touch addresses inside the
  MMIO register windows announced by the boot stub (`boot_windows`), hardened with the proved
  branchless `in_bounds` mask (`Mini/WordProofs.lean`). Out-of-window access halts immediately.
- Shared DMA memory (`alloc`/`load`/`store`) lives in one page-aligned bump arena separate from
  the Lean heap and stack; Lean never receives a raw pointer.
- Framebuffer blits (`fbBlit`) write strictly inside the announced scanout buffer.
- Hardware entropy (`rndr`) executes AArch64 `RNDRRS`/`RNDR` directly and reports hardware validity. -/

namespace Kernel.Hw

/-- A device register window announced at boot (`base`, `size` in bytes). -/
structure Window where
  base : UInt64
  size : UInt64
  deriving Repr, Inhabited, BEq

/-- Announced framebuffer geometry from boot stub (or zeroed if none yet). -/
structure FbInfo where
  base : UInt64
  width : UInt32
  height : UInt32
  stride : UInt32 -- in pixels
  bpp : UInt32    -- bytes per pixel (4 for XRGB8888/RGBA8888)
  deriving Repr, Inhabited, BEq

/-- Hardware CPU feature bitmask reported by `boot/aarch64/early.c`. -/
structure CpuInfo where
  midr : UInt64
  hasDit : Bool
  ditEnabled : Bool
  hasRndr : Bool
  currentEl : UInt8
  deriving Repr, Inhabited, BEq

@[extern "silo_hw_windows"]
opaque windowsRaw : BaseIO (Array UInt64)

def windows : BaseIO (Array Window) := do
  let raw ← windowsRaw
  return (Array.range (raw.size / 2)).map fun i =>
    { base := raw[2 * i]!, size := raw[2 * i + 1]! }

/-- 32-bit MMIO register read. Halts the CPU if `address` is outside announced windows. -/
@[extern "silo_hw_read32"]
opaque read32 (address : UInt64) : BaseIO UInt32

/-- 32-bit MMIO register write. Halts the CPU if `address` is outside announced windows. -/
@[extern "silo_hw_write32"]
opaque write32 (address : UInt64) (value : UInt32) : BaseIO Unit

/-- 64-bit MMIO register read. Halts the CPU if `address` is outside announced windows. -/
@[extern "silo_hw_read64"]
opaque read64 (address : UInt64) : BaseIO UInt64

/-- 64-bit MMIO register write. Halts the CPU if `address` is outside announced windows. -/
@[extern "silo_hw_write64"]
opaque write64 (address : UInt64) (value : UInt64) : BaseIO Unit

/-- Page-aligned zeroed allocation from the DMA arena (`0` if exhausted). -/
@[extern "silo_hw_alloc"]
opaque alloc (size : USize) : BaseIO UInt64

/-- Copies `size` bytes from DMA arena address `address`. Halts if out of arena bounds. -/
@[extern "silo_hw_load"]
opaque load (address : UInt64) (size : USize) : BaseIO ByteArray

/-- Copies `bytes` into DMA arena address `address`. Halts if out of arena bounds. -/
@[extern "silo_hw_store"]
opaque store (address : UInt64) (bytes : @& ByteArray) : BaseIO Unit

/-- Copies `bytes` into framebuffer at byte offset `fbOffset`. Halts if out of framebuffer bounds. -/
@[extern "silo_hw_fb_store"]
opaque fbStore (fbOffset : UInt64) (bytes : @& ByteArray) : BaseIO Unit

/-- Bounds-checked scaled blit of a logical `srcW × srcH` `RGBA_8888` frame directly to the
    announced hardware framebuffer (`bgra = true` -> `BGRA_8888`/`XRGB8888`). -/
@[extern "silo_hw_fb_blit_rgba"]
opaque fbBlitRgba (pixels : @& ByteArray) (srcW srcH : UInt32) (bgra : UInt8) : BaseIO Unit

/-- Registers a newly allocated DMA buffer as the active framebuffer (e.g. QEMU `ramfb`). -/
@[extern "silo_hw_fb_set"]
opaque fbSet (base : UInt64) (w h stride : UInt32) : BaseIO Unit

@[extern "silo_hw_fb_info"]
opaque fbInfoRaw : BaseIO (Array UInt64)

def fbInfo : BaseIO FbInfo := do
  let a ← fbInfoRaw
  if a.size ≥ 5 then
    return { base := a[0]!, width := a[1]!.toUInt32, height := a[2]!.toUInt32,
             stride := a[3]!.toUInt32, bpp := a[4]!.toUInt32 }
  else
    return { base := 0, width := 0, height := 0, stride := 0, bpp := 0 }

/-- Raw Flattened Device Tree (DTB) bytes passed by QEMU or Pixel ABL in `x0`. -/
@[extern "silo_hw_fdt"]
opaque fdtBytes : BaseIO ByteArray

/-- Kernel command line (extracted from FDT `/chosen/bootargs`). -/
@[extern "silo_hw_command_line"]
opaque commandLine : BaseIO ByteArray

/-- Reads one 64-bit hardware random word via ARMv8.5 `RNDRRS`/`RNDR`.
Returns `(ok = 1, word)` on success or `(0, 0)` if unsupported or busy. -/
@[extern "silo_hw_rndr"]
opaque rndrRaw : BaseIO (Array UInt64)

def rndr : BaseIO (Option UInt64) := do
  let a ← rndrRaw
  if a.size ≥ 2 && a[0]! != 0 then return some a[1]! else return none

@[extern "silo_hw_cpu_info"]
opaque cpuInfoRaw : BaseIO (Array UInt64)

def cpuInfo : BaseIO CpuInfo := do
  let a ← cpuInfoRaw
  if a.size ≥ 5 then
    return { midr := a[0]!, hasDit := a[1]! != 0, ditEnabled := a[2]! != 0,
             hasRndr := a[3]! != 0, currentEl := a[4]!.toUInt8 }
  else
    return { midr := 0, hasDit := false, ditEnabled := false, hasRndr := false, currentEl := 0 }

/-- Writes diagnostic bytes to the boot serial console (PL011 / Exynos UART). -/
@[extern "silo_hw_console"]
opaque consoleWrite (bytes : @& ByteArray) : BaseIO Unit

/-- Low-power spin hint (`yield` on AArch64). -/
@[extern "silo_hw_pause"]
opaque pause : BaseIO Unit

/-- Monotonic counter tick (`CNTVCT_EL0` on AArch64). -/
@[extern "silo_hw_ticks"]
opaque ticks : BaseIO UInt64

/-- Runs the C fault-injection MMU check requested by `check=<name>` in `bootargs`. -/
@[extern "silo_hw_boot_check"]
opaque bootCheck : BaseIO UInt32

/-- Powers off / halts the CPU cleanly (PSCI `SYSTEM_OFF` in QEMU, `wfi` loop on silicon). -/
@[extern "silo_hw_halt"]
opaque halt (code : UInt32) : BaseIO Unit

end Kernel.Hw
