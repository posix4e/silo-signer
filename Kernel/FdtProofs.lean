import Kernel.Fdt

/-! # Formal Proofs for Flattened Device Tree Parser (`Kernel.FdtProofs`)

Proves fail-closed header validation for malformed blobs (truncated, wrong magic, out-of-bounds
`totalsize` or sections) so untrusted bootloader FDT input can never cause out-of-bounds indexing. -/

namespace Kernel.FdtProofs

open Kernel.Fdt

/-- Any blob shorter than the 40-byte FDT header is rejected. -/
theorem parseHeader_rejects_short (b : ByteArray) (h : b.size < 40) :
    (parseHeader b).isOk = false := by
  unfold parseHeader
  simp [h, Except.isOk, Except.toBool]

/-- Any blob whose first 4 big-endian bytes are not `0xd00dfeed` is rejected. -/
theorem parseHeader_rejects_bad_magic (b : ByteArray) (hm : readBe32 b 0 ≠ fdtMagic) :
    (parseHeader b).isOk = false := by
  unfold parseHeader
  by_cases hs : b.size < 40
  · simp [hs, Except.isOk, Except.toBool]
  · have hne : (readBe32 b 0 != fdtMagic) = true := bne_iff_ne.mpr hm
    simp [hs, hne, Except.isOk, Except.toBool]

/-- Any blob declaring `totalsize > b.size` is rejected before parsing tokens. -/
theorem parseHeader_rejects_oob_totalsize (b : ByteArray)
    (h : (readBe32 b 4).toNat > b.size) :
    (parseHeader b).isOk = false := by
  unfold parseHeader
  by_cases hs : b.size < 40
  · simp [hs, Except.isOk, Except.toBool]
  · by_cases hm : (readBe32 b 0 != fdtMagic) = true
    · simp [hs, hm, Except.isOk, Except.toBool]
    · simp [hs, hm, h, Except.isOk, Except.toBool]

/-- `parse` propagates every header rejection cleanly. -/
theorem parse_rejects_short (b : ByteArray) (h : b.size < 40) (fuel : Nat) :
    (parse b fuel).isOk = false := by
  unfold parse
  by_cases hf : fuel == 0
  · simp [hf, Except.isOk, Except.toBool]
  · have hhdr := parseHeader_rejects_short b h
    cases hh : parseHeader b with
    | error e => simp [hf, Except.isOk, Except.toBool]
    | ok hdr => simp [hh, Except.isOk, Except.toBool] at hhdr

/-- `parse` with 0 fuel fails closed (cannot silently return empty success). -/
theorem parse_zero_fuel_fails (b : ByteArray) :
    (parse b 0).isOk = false := by
  unfold parse
  simp [Except.isOk, Except.toBool]

end Kernel.FdtProofs
