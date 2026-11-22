import Tricorder.Ui.State

/-! # Formal security proofs for Tricorder's state machine

All theorems are proved on Lean's three standard axioms (no `sorry`) and checked by `Tricorder/Gate.lean`:
1. `pause_wipes_secrets`: backgrounding (`Event.appPaused`) ALWAYS wipes `secrets` and `wallet` and emits no effects.
2. `ten_wrong_pins_wipes`: reaching `Vault.maxFailedAttempts` (10) wipes `hasVault`, `secrets`, `wallet`,
   returns to `.setupChoice`, and emits `[Effect.wipeVault]`.
3. `locked_cannot_sign`: whenever `m.secrets = none`, NO UI tap can emit `Effect.executeSign`.
4. `sign_requires_armed_review`: emitting `Effect.executeSign tx` from any UI tap REQUIRES
   `btn = .confirmSign`, `m.secrets.isSome = true`, and `m.screen = .reviewTx tx true`.
5. `Safe` invariant: locked and setup screens never hold unlocked secrets in `m.secrets`, preserved by
   `Model.initial`, `appPaused`, and every `tapButton`. -/

namespace Tricorder.Proofs

open Tricorder.Ui Tricorder.Signer

/-- Core memory-hygiene invariant: locked and setup screens hold zero unlocked secrets. -/
def Safe (m : Model) : Prop :=
  m.screen.isLockedOrSetup = true → m.secrets = none

theorem initial_safe (net : Network) (hasVault : Bool) (attempts : Nat) :
    Safe (Model.initial net hasVault attempts) := by
  intro _
  rfl

theorem lockModel_safe (m : Model) (msg : String) : Safe (lockModel m msg) := by
  intro _
  rfl

/-- Lock/suspend event unconditionally wipes secrets and emits no effects. -/
theorem pause_wipes_secrets (m : Model) :
    (update m .appPaused).1.secrets = none ∧
    (update m .appPaused).1.wallet = none ∧
    (update m .appPaused).2 = [] := by
  simp [update, lockModel]

/-- Ten failed PIN attempts always wipe the vault and clear all secrets. -/
theorem ten_wrong_pins_wipes (m : Model) (attempts : Nat) (wiped : Bool)
    (h : attempts ≥ Vault.maxFailedAttempts) :
    let r := update m (.hostUnlockFailed attempts wiped)
    r.1.hasVault = false ∧ r.1.secrets = none ∧ r.1.wallet = none ∧
    r.1.screen = .setupChoice ∧ r.2 = [.wipeVault] := by
  have hcond : (wiped || decide (attempts ≥ Vault.maxFailedAttempts)) = true := by
    simp [h]
  simp [update, hcond]

/-- Helper: whenever `Effect.executeSign tx` appears in `(update m (.tapButton btn)).2`,
it can only have come from `.reviewTx tx true` + `.confirmSign` while unlocked (`m.secrets.isSome`). -/
theorem sign_requires_armed_review (m : Model) (btn : ButtonId) (tx : ReviewedTx)
    (h : ∃ e ∈ (update m (.tapButton btn)).2, e = .executeSign tx) :
    btn = .confirmSign ∧ m.secrets.isSome = true ∧ m.screen = .reviewTx tx true := by
  rcases h with ⟨e, hmem, rfl⟩
  cases hs : m.screen with
  | locked =>
    cases btn <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | setupChoice =>
    cases btn <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | setupWords words page =>
    cases btn <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | setupRestore entered pref =>
    cases btn <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | setupPin words first? buf =>
    cases first? <;> cases btn <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | home =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
  | keys tab =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
  | inbox entries =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
    all_goals split at hmem <;> simp_all
  | reviewDescriptor fn wal =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
  | reviewTx tx' armed =>
    cases armed
    · cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
    · cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
  | signed res =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]
  | diagnostics dig big ent =>
    cases btn <;> cases hsec : m.secrets <;> simp_all [update, updateTap]

/-- When Tricorder holds no unlocked secrets (`m.secrets = none`), NO tap can trigger signing. -/
theorem locked_cannot_sign (m : Model) (btn : ButtonId) (hlocked : m.secrets = none) :
    ∀ e ∈ (update m (.tapButton btn)).2, e.isSign = false := by
  intro e hmem
  cases he : e with
  | executeSign tx =>
    have ⟨_, hsome, _⟩ := sign_requires_armed_review m btn tx ⟨e, hmem, he⟩
    simp [hlocked] at hsome
  | _ => rfl

/-- Every UI tap preserves `Safe` (locked & setup screens never carry unlocked secrets). -/
theorem tap_preserves_safe (m : Model) (btn : ButtonId) (hsafe : Safe m) :
    Safe (update m (.tapButton btn)).1 := by
  intro hlock
  cases hs : m.screen with
  | locked =>
    have hnone : m.secrets = none := hsafe (by simp [hs, Screen.isLockedOrSetup])
    cases btn <;> simp only [update, updateTap, hs, hnone, lockModel] at hlock ⊢
    all_goals first | rfl | (split <;> simp [hnone])
  | setupChoice =>
    have hnone : m.secrets = none := hsafe (by simp [hs, Screen.isLockedOrSetup])
    cases btn <;> simp only [update, updateTap, hs, hnone, lockModel] at hlock ⊢
    all_goals first | rfl
  | setupWords words page =>
    have hnone : m.secrets = none := hsafe (by simp [hs, Screen.isLockedOrSetup])
    cases btn <;> simp only [update, updateTap, hs, hnone, lockModel] at hlock ⊢
    all_goals first | rfl | (split <;> simp)
  | setupRestore entered pref =>
    have hnone : m.secrets = none := hsafe (by simp [hs, Screen.isLockedOrSetup])
    cases btn <;> simp only [update, updateTap, hs, hnone, lockModel] at hlock ⊢
    all_goals first | rfl | (split <;> simp [hnone])
  | setupPin words first? buf =>
    have hnone : m.secrets = none := hsafe (by simp [hs, Screen.isLockedOrSetup])
    cases first? <;> cases btn <;> simp only [update, updateTap, hs, hnone, lockModel] at hlock ⊢
    all_goals first | rfl | (split <;> simp [hnone])
  | home =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction
  | keys tab =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction
  | inbox entries =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction | (rename_i idx _; cases hget : entries[idx]? <;> simp [hs, hget] at hlock ⊢)
  | reviewDescriptor fn wal =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction
  | reviewTx tx armed =>
    cases armed <;> cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction
  | signed res =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction
  | diagnostics dig big ent =>
    cases btn <;> cases hsec : m.secrets <;> simp only [update, updateTap, hs, hsec, lockModel, Screen.isLockedOrSetup] at hlock ⊢
    all_goals first | rfl | contradiction

end Tricorder.Proofs
