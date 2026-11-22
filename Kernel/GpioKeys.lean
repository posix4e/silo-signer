/-! # Verified Debounced Physical-Button Input Machine (`Kernel.GpioKeys`)

Drives Tricorder purely from the Pixel's three physical hardware keys (or QEMU keyboard keys):
- **Volume Up** (`prev`): move LCARS focus backward
- **Volume Down** (`next`): move LCARS focus forward
- **Power** (`select`): activate focused LCARS control
- **Volume Up + Volume Down chord** (`back`): back / immediate RAM-wipe lock!

Anti-bounce & anti-accidental-signing guarantees (proved in `Kernel/GpioKeysProofs.lean`):
1. A button must sample pressed for `debounceTicks` (= 3) consecutive polls before firing.
2. Once fired, holding the button NEVER re-triggers until it is fully released (prevents holding
   Power from accidentally arming AND confirming a Bitcoin transaction!). -/

namespace Kernel.GpioKeys

/-- Semantic physical-button events delivered to Tricorder's LCARS UI. -/
inductive KeyEvent where
  | prev   -- Volume Up
  | next   -- Volume Down
  | select -- Power
  | back   -- VolUp + VolDown chord (Back / Lock)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Raw instantaneous GPIO sample of the 3 physical buttons (`true` = physically pressed). -/
structure RawSample where
  volUp : Bool := false
  volDown : Bool := false
  power : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Per-button debouncer requiring `debounceTicks` consecutive high polls and explicit release. -/
structure ButtonLatch where
  streak : Nat := 0
  latched : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

def debounceTicks : Nat := 3

/-- Steps one `ButtonLatch` with a new boolean sample. Returns `(nextLatch, firedRisingEdge)`. -/
def ButtonLatch.step (st : ButtonLatch) (pressed : Bool) : ButtonLatch × Bool :=
  if !pressed then
    ({ streak := 0, latched := false }, false)
  else if st.latched then
    ({ st with streak := debounceTicks }, false)
  else
    let nextStreak := st.streak + 1
    if nextStreak ≥ debounceTicks then
      ({ streak := debounceTicks, latched := true }, true)
    else
      ({ streak := nextStreak, latched := false }, false)

/-- Complete debounced state for all 3 hardware buttons + chord latch. -/
structure KeysState where
  up : ButtonLatch := {}
  down : ButtonLatch := {}
  power : ButtonLatch := {}
  chord : ButtonLatch := {}
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Steps the 3-button debouncer and emits at most one `KeyEvent` per poll.
Chord (`volUp && volDown`) takes priority and suppresses individual up/down firing. -/
def KeysState.poll (st : KeysState) (s : RawSample) : KeysState × Option KeyEvent :=
  let both := s.volUp && s.volDown
  let (chord', chordFired) := st.chord.step both
  let (up', upFired) := st.up.step (s.volUp && !both)
  let (down', downFired) := st.down.step (s.volDown && !both)
  let (pow', powFired) := st.power.step (s.power && !both)
  let ev? :=
    if chordFired then some .back
    else if powFired then some .select
    else if upFired then some .prev
    else if downFired then some .next
    else none
  ({ up := up', down := down', power := pow', chord := chord' }, ev?)

end Kernel.GpioKeys
