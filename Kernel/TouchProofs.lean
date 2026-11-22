import Kernel.Touch

/-! # What a tap is (`Kernel.TouchProofs`)

1. `down_never_taps`: a finger going down, or moving, taps nothing.
2. `tap_is_a_still_lift`: a tap comes only from a lift, of a touch that did not move, at the place it began.
3. `lift_forgets`: after a lift nothing is held over, so one touch gives at most one tap.
4. `moved_stays_moved`: a touch that has moved too far stays one that has, wherever the finger goes next. -/

namespace Kernel.TouchProofs

open Kernel.Touch

theorem down_never_taps (s : TapState) (p : Point) : (s.step (.down p)).2 = none := by
  unfold TapState.step
  cases s.start? <;> rfl

theorem tap_is_a_still_lift (s : TapState) (sample : Sample) (at_ : Point)
    (h : (s.step sample).2 = some at_) :
    sample = .up ∧ s.start? = some at_ ∧ s.moved = false := by
  cases sample with
  | down p => rw [down_never_taps] at h; cases h
  | up =>
    unfold TapState.step at h
    cases hs : s.start? with
    | none => simp [hs] at h
    | some a =>
      simp only [hs] at h
      cases hm : s.moved with
      | true => simp [hm] at h
      | false => simp [hm] at h; exact ⟨rfl, by rw [h], rfl⟩

theorem lift_forgets (s : TapState) : (s.step .up).1 = {} := by
  unfold TapState.step
  cases s.start? <;> rfl

theorem moved_stays_moved (s : TapState) (p a : Point) (hs : s.start? = some a) (hm : s.moved = true) :
    (s.step (.down p)).1.moved = true := by
  unfold TapState.step
  simp [hs, hm]

end Kernel.TouchProofs
