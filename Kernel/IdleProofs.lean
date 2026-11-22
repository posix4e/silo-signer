import Kernel.Idle

/-! # What a dark panel can and cannot do (`Kernel.IdleProofs`)

1. `off_never_delivers`: dark, no input reaches the screens. A press on a dark panel signs nothing.
2. `lock_is_the_lock_clock`: whether to lock is decided from the lock clock alone, lit or dark, whatever the
   input: the signer is unlocked no longer than it was before there was a dark panel.
3. `only_a_person_sets_the_lock_clock`: nothing but a press or a tap sets the lock clock back, so the cable
   and a stray touch cannot hold the signer unlocked.
4. `wake_after_lock_time_locks`: lighting the panel once the lock time has passed comes with the lock.
5. `input_when_off_wakes`: dark, any input lights the panel.
6. `quiet_when_off_stays_off`: dark and nothing happening, it stays dark and nothing is drawn.
7. `blank_only_from_quiet`: the panel goes dark only when it was lit, nothing happened, and the screen clock
   has run out.
8. `on_delivers`: lit, a press or a tap is passed on and the panel stays lit. -/

namespace Kernel.IdleProofs

open Kernel.Idle

theorem off_never_delivers (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input)
    (h : s.phase = .off) : (step cfg s unlocked now i).deliver = false := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp_all [step]

theorem lock_is_the_lock_clock (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input) :
    (step cfg s unlocked now i).lock = (unlocked && decide (now - s.lastPerson ≥ cfg.lockTicks)) := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp [step, lockDue] <;> split <;> rfl

theorem only_a_person_sets_the_lock_clock (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input)
    (h : i.isPerson = false) : (step cfg s unlocked now i).state.lastPerson = s.lastPerson := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp_all [step, Input.isPerson] <;> split <;> rfl

theorem wake_after_lock_time_locks (cfg : Config) (s : State) (now : Nat) (i : Input)
    (hdue : now - s.lastPerson ≥ cfg.lockTicks) (_hw : (step cfg s true now i).wake = true) :
    (step cfg s true now i).lock = true := by
  rw [lock_is_the_lock_clock]
  simp [hdue]

theorem input_when_off_wakes (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input)
    (h : s.phase = .off) (hi : i ≠ .none) :
    (step cfg s unlocked now i).wake = true ∧ (step cfg s unlocked now i).state.phase = .on := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp_all [step]

theorem quiet_when_off_stays_off (cfg : Config) (s : State) (unlocked : Bool) (now : Nat)
    (h : s.phase = .off) :
    (step cfg s unlocked now .none).state = s ∧ (step cfg s unlocked now .none).wake = false := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> simp_all [step]

theorem blank_only_from_quiet (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input)
    (h : (step cfg s unlocked now i).blank = true) :
    s.phase = .on ∧ i = .none ∧ now - s.lastScreen ≥ cfg.screenOffTicks := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp [step] at h ⊢
  split at h <;> simp_all

theorem on_delivers (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input)
    (h : s.phase = .on) (hi : i.isPerson = true) :
    (step cfg s unlocked now i).deliver = true ∧ (step cfg s unlocked now i).state.phase = .on := by
  obtain ⟨phase, lp, ls⟩ := s
  cases phase <;> cases i <;> simp_all [step, Input.isPerson]

end Kernel.IdleProofs
