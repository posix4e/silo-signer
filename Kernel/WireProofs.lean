import Kernel.Wire

/-! # Formal Proofs for Wire Framing & Protocol Gating (`Kernel.WireProofs`)

Proves:
1. `op_roundtrip`: every `Op` byte-encoding round-trips cleanly.
2. `locked_blocks_privileged`: when the device is locked, `getKeys`, `pushDescriptor`, `pushOverride` and
   `pollResult` are denied.
3. `reviewing_blocks_push`: while a wallet or a payment is on the screen for review, the host can put
   nothing in its place.
4. `only_test_builds_inject_keys`: the host can press the buttons only in a regtest build. On signet and
   mainnet only the physical buttons operate the signer.
5. `decode_rejects_short` and `decode_rejects_bad_magic`: malformed and truncated frames are refused. -/

namespace Kernel.WireProofs

open Kernel.Wire

/-- Every `Op` survives `toByte` -> `ofByte?` without collision or loss. -/
theorem op_roundtrip (op : Op) : Op.ofByte? op.toByte = some op := by
  cases op <;> rfl

/-- When the signer is locked, every key-export, descriptor, PSBT, and signature-poll op is refused. -/
theorem locked_blocks_privileged (op : Op) (reviewing testBuild : Bool)
    (h : op.requiresUnlocked = true) :
    op.allowed false reviewing testBuild = false := by
  simp [Op.allowed, h]

/-- While a wallet or a payment is on the screen for review, the host can put nothing in its place. -/
theorem reviewing_blocks_push (op : Op) (unlocked testBuild : Bool)
    (h : op.isPush = true) :
    op.allowed unlocked true testBuild = false := by
  cases unlocked <;> simp [Op.allowed, h]

/-- Outside a regtest build, host key injection (`injectKey`) is refused, whatever else is true. -/
theorem only_test_builds_inject_keys (unlocked reviewing : Bool) :
    Op.injectKey.allowed unlocked reviewing false = false := by
  simp [Op.allowed, Op.requiresUnlocked, Op.isPush, Op.isTestOnly]

/-- Outside a regtest build the host can neither read nor write a device register (`lab`). -/
theorem only_test_builds_touch_registers (unlocked reviewing : Bool) :
    Op.lab.allowed unlocked reviewing false = false := by
  simp [Op.allowed, Op.requiresUnlocked, Op.isPush, Op.isTestOnly]

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
