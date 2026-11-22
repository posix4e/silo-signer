import Kernel.VaultStore

/-! # Formal Proofs for Zero-Filesystem 2-Slot Vault Persistence (`Kernel.VaultStoreProofs`)

Machine-checked crash-consistency and wipe theorems for `Kernel.VaultStore`:
1. `decodeSlot_zeroSlot`: an all-zero wiped block is NEVER accepted as valid.
2. `planWrite_targets_inactive`: committing NEVER overwrites the active committed slot.
3. `crash_consistency_torn_write`: if power is lost mid-write and the target slot is left with
   ANY corrupted bytes `corrupt` that fail authentication (`decodeSlot corrupt = none`),
   `recover` STILL recovers the exact prior committed `SlotRecord`!
4. `wipeBoth_erases_all`: after `wipeBoth`, `recover` returns `none`. -/

namespace Kernel.VaultStoreProofs

open Kernel.VaultStore

/-- Standard-axiom O(1) proof that an all-zero wiped block is rejected (`zeroSlot.get! 0 = 0 ≠ 0x54`). -/
theorem decodeSlot_zeroSlot_pure : decodeSlot zeroSlot = none := by
  have hz : zeroSlot.get! 0 = 0 := by
    change (Array.replicate slotBytes (0 : UInt8))[0]! = 0
    rw [getElem!_pos (Array.replicate slotBytes (0 : UInt8)) 0 (by simp [slotBytes])]
    simp
  unfold decodeSlot
  simp [hz]

/-- Writing ALWAYS targets the inactive slot (`target ≠ activeIdx`), never clobbering the active slot. -/
theorem planWrite_targets_inactive (d : DualDisk) (activeIdx : SlotIdx) (r : SlotRecord)
    (h : recover d = some (activeIdx, r)) :
    (planWrite d).1 ≠ activeIdx := by
  unfold planWrite
  rw [h]
  cases activeIdx <;> simp

/-- **Crash-Consistency (Torn Write) Theorem**:
Suppose the disk currently recovers `(activeIdx, r)`. We begin writing the next state to
`targetIdx := (planWrite d).1`, and power cuts mid-write leaving `targetIdx` containing ANY
corrupted bytes `torn` that fail SHA-256/header validation (`decodeSlot torn = none`).
Then `recover (d.set targetIdx torn)` STILL returns `some (activeIdx, r)`! -/
theorem crash_consistency_torn_write (d : DualDisk) (activeIdx : SlotIdx) (r : SlotRecord)
    (torn : ByteArray)
    (hrec : recover d = some (activeIdx, r))
    (htorn : decodeSlot torn = none) :
    recover (d.set (planWrite d).1 torn) = some (activeIdx, r) := by
  unfold planWrite
  rw [hrec]
  unfold recover at hrec ⊢
  cases h0 : decodeSlot d.slot0 <;> cases h1 : decodeSlot d.slot1 <;>
    simp [h0, h1] at hrec
  · -- slot0 = none, slot1 = some r1 -> activeIdx = true, target = false
    obtain ⟨rfl, rfl⟩ := hrec
    simp [DualDisk.set, htorn, h1]
  · -- slot0 = some r0, slot1 = none -> activeIdx = false, target = true
    obtain ⟨rfl, rfl⟩ := hrec
    simp [DualDisk.set, htorn, h0]
  · -- both valid: whichever had higher seq is activeIdx; writing !activeIdx preserves activeIdx!
    rename_i r0 r1
    by_cases hgt : r1.seq > r0.seq
    · simp [hgt] at hrec
      obtain ⟨rfl, rfl⟩ := hrec
      simp [DualDisk.set, htorn, h1]
    · simp [hgt] at hrec
      obtain ⟨rfl, rfl⟩ := hrec
      simp [DualDisk.set, htorn, h0]

/-- **Monotonic Commit Theorem**:
If a commit to `targetIdx := (planWrite d).1` finishes cleanly and decodes as `rNew` with
`rNew.seq = (planWrite d).2`, then `recover` strictly selects `rNew`! -/
theorem monotonic_commit_wins (d : DualDisk) (activeIdx : SlotIdx) (rOld rNew : SlotRecord)
    (blk : ByteArray)
    (hrec : recover d = some (activeIdx, rOld))
    (hdec : decodeSlot blk = some rNew)
    (hseq : rNew.seq = (planWrite d).2) :
    recover (d.set (planWrite d).1 blk) = some (!activeIdx, rNew) := by
  have hplan : planWrite d = (!activeIdx, rOld.seq + 1) := by
    unfold planWrite; rw [hrec]
  rw [hplan] at hseq ⊢
  simp only at hseq ⊢
  unfold recover at hrec ⊢
  cases h0 : decodeSlot d.slot0 <;> cases h1 : decodeSlot d.slot1 <;>
    simp [h0, h1] at hrec
  · obtain ⟨rfl, rfl⟩ := hrec
    simp [DualDisk.set, hdec, h1]
    omega
  · obtain ⟨rfl, rfl⟩ := hrec
    simp [DualDisk.set, hdec, h0]
    omega
  · rename_i r0 r1
    by_cases hgt : r1.seq > r0.seq
    · simp [hgt] at hrec
      obtain ⟨rfl, rfl⟩ := hrec
      simp [DualDisk.set, hdec, h1]
      omega
    · simp [hgt] at hrec
      obtain ⟨rfl, rfl⟩ := hrec
      simp [DualDisk.set, hdec, h0]
      omega

/-- **Wipe Soundness Theorem**: After `wipeBoth`, `recover` returns `none`. -/
theorem wipeBoth_erases_all (d : DualDisk) :
    recover (wipeBoth d) = none := by
  simp [wipeBoth, recover, decodeSlot_zeroSlot_pure]

end Kernel.VaultStoreProofs
