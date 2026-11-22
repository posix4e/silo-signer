import Kernel.Fb

/-! # Formal Proofs for Framebuffer Bounds Safety (`Kernel.FbProofs`)

Proves that nearest-neighbor scaling coordinates and scanline byte offsets remain strictly inside
source and destination framebuffer bounds for all non-zero geometries. -/

namespace Kernel.FbProofs

open Kernel.Fb

/-- Nearest-neighbor X/Y source index stays strictly below `srcDim` whenever `dstIdx < dstDim` and `srcDim > 0`. -/
theorem scale_coord_in_bounds (dstIdx dstDim srcDim : Nat)
    (hidx : dstIdx < dstDim) (hsrc : srcDim > 0) :
    (dstIdx * srcDim) / dstDim < srcDim := by
  have hpos : dstDim > 0 := by omega
  rw [Nat.div_lt_iff_lt_mul hpos]
  have : dstIdx * srcDim < dstDim * srcDim := Nat.mul_lt_mul_of_pos_right hidx hsrc
  simpa [Nat.mul_comm] using this

/-- Every scanline write at `y < dstH` with `dstW ≤ stride` fits strictly inside `dstH * stride * 4` bytes. -/
theorem scanline_offset_in_bounds (y dstW dstH stride : Nat)
    (hy : y < dstH) (hs : dstW ≤ stride) :
    pixelByteOffset 0 y stride + dstW * 4 ≤ dstH * stride * 4 := by
  unfold pixelByteOffset
  have h1 : y + 1 ≤ dstH := hy
  have h2 : y * stride + dstW ≤ (y + 1) * stride := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_left hs (y * stride)
  have h3 : (y + 1) * stride ≤ dstH * stride := Nat.mul_le_mul_right stride h1
  omega

/-- Every individual pixel `(x, y)` inside `dstW × dstH` with `dstW ≤ stride` fits inside `dstH * stride * 4` bytes. -/
theorem pixel_offset_in_bounds (x y dstW dstH stride : Nat)
    (hx : x < dstW) (hy : y < dstH) (hs : dstW ≤ stride) :
    pixelByteOffset x y stride + 4 ≤ dstH * stride * 4 := by
  unfold pixelByteOffset
  have h1 : y + 1 ≤ dstH := hy
  have h2 : y * stride + x + 1 ≤ (y + 1) * stride := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have h3 : (y + 1) * stride ≤ dstH * stride := Nat.mul_le_mul_right stride h1
  omega

end Kernel.FbProofs
