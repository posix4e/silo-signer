import Kernel.UsbLink

/-! # The record of the USB link stays small and keeps the present (`Kernel.UsbLinkProofs`)

1. `note_bounded`: a record within its bound stays within it, so it cannot grow for as long as the signer runs.
2. `note_keeps_newest`: after a look, the newest state kept shows the same link as that look. -/

namespace Kernel.UsbLinkProofs

open Kernel.UsbLink

theorem note_bounded (log : List Sample) (s : Sample) (h : log.length ≤ bound) :
    (note log s).length ≤ bound := by
  cases log with
  | nil => simp [note, bound]
  | cons last rest =>
    simp only [note]
    split
    · exact h
    · simp [bound, List.length_take]; omega

theorem note_keeps_newest (log : List Sample) (s : Sample) :
    ∃ x, (note log s).head? = some x ∧ x.same s = true := by
  cases log with
  | nil => exact ⟨s, by simp [note], by simp [Sample.same]⟩
  | cons last rest =>
    by_cases hs : last.same s = true
    · exact ⟨last, by simp [note, hs], hs⟩
    · exact ⟨s, by simp [note, hs], by simp [Sample.same]⟩

end Kernel.UsbLinkProofs
