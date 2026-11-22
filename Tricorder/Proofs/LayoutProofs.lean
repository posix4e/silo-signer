import Tricorder.Ui.Layout

/-! # Formal proofs for LCARS layout and touch hit-testing

Because `View.view` emits every interactive control as a single `DrawCmd.button`, touch hit-testing
and pixel rendering read the exact same rectangles:
1. `hitTest_sound`: any button returned by `hitTest` was rendered at a rectangle containing `(px, py)`.
2. `hitTest_complete`: if all button rectangles in `cmds` are pairwise disjoint, tapping inside any
   rendered button's rectangle returns that exact button. -/

namespace Tricorder.Proofs

open Tricorder.Ui

theorem Rect.disjoint_not_both {a b : Rect} {px py : Nat}
    (hd : Rect.disjoint a b = true) (ha : a.contains px py = true) :
    b.contains px py = false := by
  simp only [Rect.disjoint, Rect.contains, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hd ha ⊢
  omega

/-- Every hit returned by `hitTest` corresponds to a rendered `DrawCmd.button` whose rect contains `(px, py)`. -/
theorem hitTest_sound : ∀ (cmds : List DrawCmd) (px py : Nat) (id : ButtonId),
    hitTest cmds px py = some id →
    ∃ r, (id, r) ∈ buttonsOf cmds ∧ r.contains px py = true
  | [], _, _, _, h => by simp [hitTest] at h
  | .button bid r _ _ _ _ _ :: rest, px, py, id, h => by
    simp only [hitTest] at h
    split at h
    · rename_i hc
      cases h
      exact ⟨r, by simp [buttonsOf], hc⟩
    · obtain ⟨r', hmem, hc⟩ := hitTest_sound rest px py id h
      exact ⟨r', by simp [buttonsOf, hmem], hc⟩
  | .rect .. :: rest, px, py, id, h
  | .pill .. :: rest, px, py, id, h
  | .elbowTop .. :: rest, px, py, id, h
  | .elbowBottom .. :: rest, px, py, id, h
  | .text .. :: rest, px, py, id, h
  | .textCentered .. :: rest, px, py, id, h
  | .qr .. :: rest, px, py, id, h => by
    simp only [hitTest] at h
    obtain ⟨r', hmem, hc⟩ := hitTest_sound rest px py id h
    exact ⟨r', by simp [buttonsOf, hmem], hc⟩

/-- Pairwise disjointness over a list of `(ButtonId × Rect)`. -/
def PairwiseDisjoint : List (ButtonId × Rect) → Prop
  | [] => True
  | (_, r) :: rest => (∀ p ∈ rest, Rect.disjoint r p.2 = true) ∧ PairwiseDisjoint rest

/-- If all buttons in `cmds` have pairwise-disjoint rectangles, tapping inside any rendered button hits it. -/
theorem hitTest_complete : ∀ (cmds : List DrawCmd) (px py : Nat) (id : ButtonId) (r : Rect),
    PairwiseDisjoint (buttonsOf cmds) →
    (id, r) ∈ buttonsOf cmds →
    r.contains px py = true →
    hitTest cmds px py = some id
  | [], _, _, _, _, _, hmem, _ => by simp [buttonsOf] at hmem
  | .button bid br _ _ _ _ _ :: rest, px, py, id, r, hpd, hmem, hc => by
    simp only [buttonsOf, List.mem_cons, PairwiseDisjoint] at hpd hmem
    rcases hmem with heq | hrest
    · cases heq
      simp [hitTest, hc]
    · have hdisj : Rect.disjoint br r = true := hpd.1 (id, r) hrest
      have hnot : br.contains px py = false := by
        have hsym : Rect.disjoint r br = true := by
          simp only [Rect.disjoint, Bool.or_eq_true, decide_eq_true_eq] at hdisj ⊢
          omega
        exact Rect.disjoint_not_both hsym hc
      simp only [hitTest, hnot, Bool.false_eq_true, ↓reduceIte]
      exact hitTest_complete rest px py id r hpd.2 hrest hc
  | .rect .. :: rest, px, py, id, r, hpd, hmem, hc
  | .pill .. :: rest, px, py, id, r, hpd, hmem, hc
  | .elbowTop .. :: rest, px, py, id, r, hpd, hmem, hc
  | .elbowBottom .. :: rest, px, py, id, r, hpd, hmem, hc
  | .text .. :: rest, px, py, id, r, hpd, hmem, hc
  | .textCentered .. :: rest, px, py, id, r, hpd, hmem, hc
  | .qr .. :: rest, px, py, id, r, hpd, hmem, hc => by
    simp only [buttonsOf, hitTest] at hpd hmem ⊢
    exact hitTest_complete rest px py id r hpd hmem hc

/-- Physical-button focus ALWAYS selects a real button rendered on the current screen (never out of bounds). -/
theorem focusedButton_is_member (cmds : List DrawCmd) (idx : Nat) (id : ButtonId)
    (h : focusedButton? cmds idx = some id) :
    ∃ r, (id, r) ∈ buttonsOf cmds := by
  unfold focusedButton? focusedTarget? at h
  cases hbs : buttonsOf cmds with
  | nil => simp [hbs] at h
  | cons b bs =>
    simp only [hbs, Option.map_eq_some_iff] at h
    obtain ⟨⟨bid, r⟩, hget, rfl⟩ := h
    exact ⟨r, List.mem_of_getElem? hget⟩

end Tricorder.Proofs
