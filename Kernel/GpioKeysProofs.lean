import Kernel.GpioKeys

/-! # Formal Proofs for Physical-Button Debouncer (`Kernel.GpioKeysProofs`)

Proves:
1. `single_glitch_never_fires`: a single-poll noise glitch from idle NEVER fires a button event.
2. `two_tick_glitch_never_fires`: even a 2-tick transient glitch from idle NEVER fires.
3. `latched_never_refires`: once a button fires (`latched = true`), keeping it held down NEVER
   emits a second event (prevents holding Power from accidentally arming and confirming a tx!).
4. `release_resets_latch`: releasing the button clears `latched` and `streak`. -/

namespace Kernel.GpioKeysProofs

open Kernel.GpioKeys

/-- From idle (`streak = 0, latched = false`), a single pressed sample NEVER fires. -/
theorem single_glitch_never_fires :
    (({} : ButtonLatch).step true).2 = false := by
  decide

/-- Even two consecutive pressed samples from idle NEVER fire (requires 3). -/
theorem two_tick_glitch_never_fires :
    let (s1, _) := ({} : ButtonLatch).step true
    (s1.step true).2 = false := by
  decide

/-- Three consecutive pressed samples from idle fire once and set `latched = true`. -/
theorem three_ticks_fires_and_latches :
    let (s1, _) := ({} : ButtonLatch).step true
    let (s2, _) := s1.step true
    let (s3, fired) := s2.step true
    fired = true ∧ s3.latched = true := by
  decide

/-- **No Auto-Repeat Theorem**: Once latched (button held down), it NEVER fires again until released. -/
theorem latched_never_refires (st : ButtonLatch) (hl : st.latched = true) (pressed : Bool) :
    (st.step pressed).2 = false := by
  cases pressed <;> simp [ButtonLatch.step, hl]

/-- Releasing a button resets both `streak` and `latched` without firing. -/
theorem release_resets_latch (st : ButtonLatch) :
    st.step false = ({ streak := 0, latched := false }, false) := by
  simp [ButtonLatch.step]

/-- From an idle `KeysState`, a single-tick glitch on ANY combination of buttons emits `none`. -/
theorem single_glitch_keys_none (s : RawSample) :
    (({} : KeysState).poll s).2 = none := by
  cases s with
  | mk u d p => cases u <;> cases d <;> cases p <;> decide

end Kernel.GpioKeysProofs
