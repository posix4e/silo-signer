import Lean
import Proofs
import SecpCt.Gate
import Kernel.MmuProofs
import Kernel.FdtProofs
import Kernel.RngProofs
import Kernel.VaultStoreProofs
import Kernel.WireProofs
import Kernel.FbProofs
import Kernel.GpioKeysProofs
import Kernel.TouchProofs
import Kernel.IdleProofs
import Kernel.Dwc3Proofs
import Tricorder.Proofs.LayoutProofs
import Tricorder.Proofs.StateProofs

/-! # Tricorder Bare-Metal OS Proof Gate

Fails the build if any theorem Tricorder OS relies on depends on `sorryAx`, `Lean.ofReduceBool`,
or any axiom outside Lean's standard three (`propext`, `Quot.sound`, `Classical.choice`). -/

open Lean Elab Command

private def allowedAxioms : List Name :=
  [`propext, `Quot.sound, `Classical.choice]

private def checkAxiomsOf (name : Name) : CommandElabM Unit := do
  let axioms ← liftCoreM (Lean.collectAxioms name)
  for ax in axioms do
    if !allowedAxioms.contains ax then
      throwError "proof gate refused: {name} depends on disallowed axiom {ax}"

elab "#gate_axioms " id:ident : command => do
  let name ← liftCoreM (resolveGlobalConstNoOverload id)
  checkAxiomsOf name

-- UI & Signer State Machine Proofs
#gate_axioms Tricorder.Proofs.hitTest_sound
#gate_axioms Tricorder.Proofs.hitTest_complete
#gate_axioms Tricorder.Proofs.focusedButton_is_member
#gate_axioms Tricorder.Proofs.initial_safe
#gate_axioms Tricorder.Proofs.pause_wipes_secrets
#gate_axioms Tricorder.Proofs.ten_wrong_pins_wipes
#gate_axioms Tricorder.Proofs.sign_requires_armed_review
#gate_axioms Tricorder.Proofs.locked_cannot_sign
#gate_axioms Tricorder.Proofs.tap_preserves_safe
#gate_axioms Tricorder.Proofs.arming_requires_last_page
#gate_axioms Tricorder.Proofs.new_review_starts_unarmed
#gate_axioms Tricorder.Proofs.wrapChars_complete

-- Verified Minimal Runtime Proofs (Zero-on-Free Heap & Big-Num Arithmetic)
#gate_axioms Mini.Alloc.empty_sound
#gate_axioms Mini.Alloc.malloc_fresh_sound
#gate_axioms Mini.Alloc.malloc_reuse_sound
#gate_axioms Mini.Alloc.free_small_sound
#gate_axioms Runtime.Big.add_value
#gate_axioms Runtime.Big.mul_value
#gate_axioms Runtime.Big.natDiv_value

-- Bare-Metal Kernel MMU (W^X, Unmapped Null & Stack Guard, Device-nGnRnE Non-Exec)
#gate_axioms Kernel.MmuProofs.encodeDescriptor_wx
#gate_axioms Kernel.MmuProofs.encodeDescriptor_no_el0_exec
#gate_axioms Kernel.MmuProofs.encodeDescriptor_device_safe
#gate_axioms Kernel.MmuProofs.encodeDescriptor_unmapped_invalid
#gate_axioms Kernel.MmuProofs.validatePlan_null_unmapped
#gate_axioms Kernel.MmuProofs.validatePlan_stack_guard_unmapped
#gate_axioms Kernel.MmuProofs.plan_address_wx

-- Bare-Metal FDT Parser (Fail-Closed Header & Total Termination)
#gate_axioms Kernel.FdtProofs.parseHeader_rejects_short
#gate_axioms Kernel.FdtProofs.parseHeader_rejects_bad_magic
#gate_axioms Kernel.FdtProofs.parseHeader_rejects_oob_totalsize
#gate_axioms Kernel.FdtProofs.parse_rejects_short
#gate_axioms Kernel.FdtProofs.parse_zero_fuel_fails

-- Bare-Metal Hardware RNG Health Checks (Fail-Closed Degenerate/Stuck Rejection)
#gate_axioms Kernel.RngProofs.wordsHealthy_rejects_zero
#gate_axioms Kernel.RngProofs.wordsHealthy_rejects_ones
#gate_axioms Kernel.RngProofs.wordsHealthy_rejects_constant
#gate_axioms Kernel.RngProofs.wordsHealthy_rejects_adj_dup
#gate_axioms Kernel.RngProofs.conditionBlock_fail_closed

-- Zero-Filesystem 2-Slot Raw Flash Vault Store (Torn-Write Crash Consistency & Wipe)
#gate_axioms Kernel.VaultStoreProofs.decodeSlot_zeroSlot_pure
#gate_axioms Kernel.VaultStoreProofs.planWrite_targets_inactive
#gate_axioms Kernel.VaultStoreProofs.crash_consistency_torn_write
#gate_axioms Kernel.VaultStoreProofs.monotonic_commit_wins
#gate_axioms Kernel.VaultStoreProofs.wipeBoth_erases_all

-- Zero-Filesystem Wire Framing & Locked/Mainnet Security Gating
#gate_axioms Kernel.WireProofs.op_roundtrip
#gate_axioms Kernel.WireProofs.locked_blocks_privileged
#gate_axioms Kernel.WireProofs.reviewing_blocks_push
#gate_axioms Kernel.WireProofs.only_test_builds_inject_keys
#gate_axioms Kernel.WireProofs.only_test_builds_touch_registers
#gate_axioms Kernel.WireProofs.decode_rejects_short
#gate_axioms Kernel.WireProofs.decode_rejects_bad_magic

-- Framebuffer Bounds & Physical-Button Anti-Glitch / Anti-Auto-Repeat
#gate_axioms Kernel.FbProofs.scale_coord_in_bounds
#gate_axioms Kernel.FbProofs.scanline_offset_in_bounds
#gate_axioms Kernel.FbProofs.pixel_offset_in_bounds
#gate_axioms Kernel.GpioKeysProofs.single_glitch_never_fires
#gate_axioms Kernel.GpioKeysProofs.two_tick_glitch_never_fires
#gate_axioms Kernel.GpioKeysProofs.three_ticks_fires_and_latches
#gate_axioms Kernel.GpioKeysProofs.latched_never_refires
#gate_axioms Kernel.TouchProofs.down_never_taps
#gate_axioms Kernel.TouchProofs.tap_is_a_still_lift
#gate_axioms Kernel.TouchProofs.lift_forgets
#gate_axioms Kernel.TouchProofs.moved_stays_moved
#gate_axioms Kernel.GpioKeysProofs.release_resets_latch
#gate_axioms Kernel.GpioKeysProofs.single_glitch_keys_none

-- Going dark when left alone: a dark panel passes nothing on, and changes nothing about locking
#gate_axioms Kernel.IdleProofs.off_never_delivers
#gate_axioms Kernel.IdleProofs.lock_is_the_lock_clock
#gate_axioms Kernel.IdleProofs.only_a_person_sets_the_lock_clock
#gate_axioms Kernel.IdleProofs.wake_after_lock_time_locks
#gate_axioms Kernel.IdleProofs.input_when_off_wakes
#gate_axioms Kernel.IdleProofs.quiet_when_off_stays_off
#gate_axioms Kernel.IdleProofs.blank_only_from_quiet
#gate_axioms Kernel.IdleProofs.on_delivers

-- Bare-Metal USB-C Synopsys DWC3 Descriptor & SETUP Bounds
#gate_axioms Kernel.Dwc3Proofs.deviceDescriptor_size
#gate_axioms Kernel.Dwc3Proofs.configDescriptor_size
#gate_axioms Kernel.Dwc3Proofs.decodeSetup_rejects_short
#gate_axioms Kernel.Dwc3Proofs.clampToWLength_le_req
#gate_axioms Kernel.Dwc3Proofs.clampToWLength_le_data
#gate_axioms Kernel.Dwc3Proofs.handleStandardSetup_sendData_bounded
