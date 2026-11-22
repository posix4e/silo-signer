import Kernel.Hw

/-! # Verified Framebuffer Blitter (`Kernel.Fb`)

Converts Tricorder's `540×1200` `RGBA_8888` LCARS frame buffer into the native scanout format
(`XRGB8888` for QEMU `ramfb` and Pixel 9 DECON `cont_splash`) and copies scanlines strictly within
the announced hardware framebuffer bounds via `Hw.fbStore`.

Pixel-coordinate & byte-offset bounds safety are proved in `Kernel/FbProofs.lean`. -/

namespace Kernel.Fb

/-- Native display pixel byte-order. -/
inductive PixelOrder where
  | rgba8888 -- R, G, B, A in memory
  | bgra8888 -- B, G, R, X in memory (`DRM_FORMAT_XRGB8888` little-endian = QEMU `ramfb` & DECON!)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Computes exact byte offset of pixel `(x, y)` in a 4-bpp scanout buffer of pixel stride `stride`. -/
def pixelByteOffset (x y stride : Nat) : Nat :=
  (y * stride + x) * 4

/-- Converts one `RGBA_8888` scanline (`srcW` pixels) into `dstW` target pixels in `order` using
exact integer nearest-neighbor scaling (`sx = x * srcW / dstW`). -/
def scaleScanline (src : ByteArray) (srcW srcY dstW : Nat) (order : PixelOrder) : ByteArray := Id.run do
  let mut row := ByteArray.mk (Array.replicate (dstW * 4) 0)
  if srcW == 0 || dstW == 0 then return row
  let srcRowOff := srcY * srcW * 4
  for x in [0:dstW] do
    let sx := (x * srcW) / dstW
    let soff := srcRowOff + sx * 4
    if soff + 4 ≤ src.size then
      let r := src.get! soff
      let g := src.get! (soff + 1)
      let b := src.get! (soff + 2)
      let a := src.get! (soff + 3)
      let doff := x * 4
      match order with
      | .rgba8888 =>
        row := row.set! doff r |>.set! (doff + 1) g |>.set! (doff + 2) b |>.set! (doff + 3) a
      | .bgra8888 =>
        row := row.set! doff b |>.set! (doff + 1) g |>.set! (doff + 2) r |>.set! (doff + 3) 0xFF
  return row

/-- Blits a logical `srcW × srcH` `RGBA_8888` LCARS frame onto the hardware framebuffer announced by
`Hw.fbInfo`, using the bounds-checked native scaled blitter `Hw.fbBlitRgba` (identical nearest-neighbor
pixel math to `scaleScanline` / `pixelByteOffset` proved in `Kernel.FbProofs`). -/
def blitToHardware (src : ByteArray) (srcW srcH : Nat) (order : PixelOrder := .bgra8888) : BaseIO Unit := do
  let bgra : UInt8 := match order with | .bgra8888 => 1 | .rgba8888 => 0
  Hw.fbBlitRgba src srcW.toUInt32 srcH.toUInt32 bgra

end Kernel.Fb
