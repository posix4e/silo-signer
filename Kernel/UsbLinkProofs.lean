import Kernel.UsbLink

/-! # The record of the USB link stays small and keeps the present (`Kernel.UsbLinkProofs`)

1. `note_bounded`: a record within its bound stays within it, so it cannot grow for as long as the signer runs.
2. `note_keeps_newest`: after a look, the newest state kept shows the same link as that look.
3. `on_never_reconnects`: a configured link that is on is never started over.
4. `busy_never_reconnects`: nor is one whose controller has reported an event since the last look, so a host
   in the middle of setting the signer up is not cut off.
5. `reconnect_only_after_quiet`: the link is started over only when it has been quiet for the whole interval.
6. `reconnect_restarts_the_clock`: and then the interval starts again, so it is at most once an interval. -/

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

theorem on_never_reconnects (q : Nat) (w : Watch) (now events : Nat) :
    (w.step q now true events).2 = .none := by
  simp [Watch.step]

theorem busy_never_reconnects (q : Nat) (w : Watch) (now events : Nat) (on : Bool) (h : events ≠ w.events) :
    (w.step q now on events).2 = .none := by
  cases on <;> simp [Watch.step, h]

theorem reconnect_only_after_quiet (q : Nat) (w : Watch) (now events : Nat) (on phy : Bool)
    (h : (w.step q now on events).2 = .reconnect phy) :
    on = false ∧ events = w.events ∧ ∃ t, w.quietSince = some t ∧ now - t ≥ q := by
  obtain ⟨qs, ev, tries⟩ := w
  cases on <;> cases qs <;> simp only [Watch.step] at h ⊢ <;> (repeat' split at h) <;> simp_all

theorem reconnect_restarts_the_clock (q : Nat) (w : Watch) (now events : Nat) (on phy : Bool)
    (h : (w.step q now on events).2 = .reconnect phy) :
    (w.step q now on events).1.quietSince = some now := by
  obtain ⟨qs, ev, tries⟩ := w
  cases on <;> cases qs <;> simp only [Watch.step] at h ⊢ <;> (repeat' split at h) <;> simp_all

end Kernel.UsbLinkProofs
