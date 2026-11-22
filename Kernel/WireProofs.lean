import Kernel.Wire

/-! # Formal Proofs for Wire Framing & Protocol Gating (`Kernel.WireProofs`)

Proves:
1. `op_roundtrip`: every `Op` byte-encoding round-trips cleanly.
2. `locked_blocks_privileged`: when the device is locked (`unlocked = false`), `getKeys`,
   `pushDescriptor`, `pushOverride`, `pushApprove`, and `pollResult` are unconditionally denied.
3. `mainnet_blocks_key_injection`: on mainnet (`isMainnet = true`), host key injection (`injectKey`)
   is unconditionally forbidden — ONLY physical hardware buttons can operate a mainnet signer!
4. `decode_rejects_short` & `decode_rejects_bad_magic`: malformed/truncated frames fail closed. -/

namespace Kernel.WireProofs

open Kernel.Wire

/-- Every `Op` survives `toByte` -> `ofByte?` without collision or loss. -/
theorem op_roundtrip (op : Op) : Op.ofByte? op.toByte = some op := by
  cases op <;> rfl

/-- When the signer is locked, every key-export, descriptor, PSBT, and signature-poll op is refused. -/
theorem locked_blocks_privileged (op : Op) (isMainnet : Bool)
    (h : op.requiresUnlocked = true) :
    op.allowed false isMainnet = false := by
  simp [Op.allowed, h]

/-- On mainnet builds, host key injection (`injectKey`) is unconditionally forbidden. -/
theorem mainnet_blocks_key_injection (unlocked : Bool) :
    Op.injectKey.allowed unlocked true = false := by
  have heq : (Op.injectKey == Op.injectKey) = true := by decide
  simp [Op.allowed, Op.requiresUnlocked, heq]

/-- Any frame shorter than 12 bytes (8-byte header + 4-byte CRC-32) is rejected. -/
theorem decode_rejects_short (raw : ByteArray) (h : raw.size < headerSize + trailerSize) :
    (decode raw).isOk = false := by
  unfold decode
  simp [h, Except.isOk, Except.toBool]

/-- Any frame without the `"TRIW"` magic prefix is rejected. -/
theorem decode_rejects_bad_magic (raw : ByteArray) (h : (raw.extract 0 4 != magic) = true) :
    (decode raw).isOk = false := by
  unfold decode
  by_cases hs : raw.size < headerSize + trailerSize
  · simp [hs, Except.isOk, Except.toBool]
  · simp [hs, h, Except.isOk, Except.toBool]

end Kernel.WireProofs
