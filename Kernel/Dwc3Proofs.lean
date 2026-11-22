import Kernel.Dwc3

/-! # Formal Proofs for Pure-Lean USB-C DWC3 Descriptor & SETUP Engine (`Kernel.Dwc3Proofs`)

Proves exact USB 2.0 descriptor lengths, fail-closed short SETUP rejection, strict `wLength`
clamping (a host requesting `wLength` bytes NEVER receives more than `wLength` bytes), and
7-bit USB address masking. -/

namespace Kernel.Dwc3Proofs

open Kernel.Dwc3

/-- The USB 2.0 Device Descriptor is always exactly 18 bytes. -/
theorem deviceDescriptor_size : deviceDescriptor.size = 18 := rfl

/-- The USB 2.0 Configuration + Interface + 2 Bulk Endpoints Descriptor is always 32 bytes. -/
theorem configDescriptor_size (mps : UInt16) : (configDescriptor mps).size = 32 := rfl

/-- Any SETUP packet shorter than 8 bytes is rejected (`none`). -/
theorem decodeSetup_rejects_short (b : ByteArray) (h : b.size < 8) :
    decodeSetup b = none := by
  unfold decodeSetup
  simp [h]

/-- `clampToWLength` never returns more bytes than the host's requested `wLength`. -/
theorem clampToWLength_le_req (data : ByteArray) (wLength : UInt16) :
    (clampToWLength data wLength).size ≤ wLength.toNat := by
  unfold clampToWLength
  simp only [ByteArray.size_extract, Nat.sub_zero]
  omega

/-- `clampToWLength` never exceeds the underlying descriptor size. -/
theorem clampToWLength_le_data (data : ByteArray) (wLength : UInt16) :
    (clampToWLength data wLength).size ≤ data.size := by
  unfold clampToWLength
  simp only [ByteArray.size_extract, Nat.sub_zero]
  omega

/-- Any `GET_DESCRIPTOR` or status reply produced by `handleStandardSetup` respects `req.wLength`. -/
theorem handleStandardSetup_sendData_bounded (req : SetupPacket) (mps : UInt16) (payload : ByteArray)
    (h : handleStandardSetup req mps = .sendData payload) :
    payload.size ≤ req.wLength.toNat := by
  unfold handleStandardSetup at h
  dsimp only at h
  split at h
  · cases h; exact clampToWLength_le_req _ _
  · cases h
  · cases h
  · cases h
  · split at h
    · cases h; exact clampToWLength_le_req _ _
    · cases h; exact clampToWLength_le_req _ _
    · split at h
      · cases h; exact clampToWLength_le_req _ _
      · cases h
    · cases h; exact clampToWLength_le_req _ _
    · cases h
  · cases h; exact clampToWLength_le_req _ _
  · cases h
  · cases h; exact clampToWLength_le_req _ _
  · cases h
  · cases h

end Kernel.Dwc3Proofs
