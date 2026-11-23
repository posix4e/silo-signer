/-! # Going dark when left alone (`Kernel.Idle`)

When the panel is lit and when it is dark, and what a press on a dark panel does. Nothing here touches
hardware: the time and what just happened go in, and what the main loop must do comes out.

There are two clocks. The lock clock is the one the signer always had: it is set back by a button press or a
tap, and by nothing else, and when it has run for `lockTicks` an unlocked signer locks. The screen clock is
set back by those and by anything else that should light the panel (a touch on the dark glass, a new picture
from the cable), and when it has run for `screenOffTicks` the panel goes dark.

A dark panel changes nothing about locking: the lock is decided from the lock clock alone, before the input
of the moment is looked at. And a press on a dark panel lights it and does nothing else, so that nobody
presses a control they cannot see.

What is proved (`Kernel/IdleProofs.lean`): dark, nothing reaches the screens; the lock is decided as it was
before there was a dark panel, and only a press or a tap sets its clock back; any input lights a dark panel;
the panel goes dark only from quiet; and lit, a press or a tap is passed on. -/

namespace Kernel.Idle

/-- How long each clock runs, in ticks of the machine's counter. -/
structure Config where
  screenOffTicks : Nat
  lockTicks : Nat
  deriving Repr, Inhabited

/-- Whether the panel is lit. -/
inductive Phase where
  | on
  | off
  deriving BEq, DecidableEq, Repr, Inhabited

/-- What happened, as far as going dark and locking care. -/
inductive Input where
  /-- Nothing. -/
  | none
  /-- A debounced button press. -/
  | key
  /-- A finished tap on the glass. -/
  | tap
  /-- Something that should light the panel and is not known to be a person's deliberate act: the touch
  controller has something to say, or the cable changed what is drawn. -/
  | stir
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A press or a tap: what sets the lock clock back. -/
def Input.isPerson : Input → Bool
  | .key | .tap => true
  | _ => false

structure State where
  phase : Phase := .on
  /-- When a person last pressed or tapped. -/
  lastPerson : Nat := 0
  /-- When the panel last had a reason to be lit. -/
  lastScreen : Nat := 0
  deriving BEq, DecidableEq, Repr, Inhabited

/-- What the main loop does about one input. -/
structure Decision where
  state : State
  /-- Wipe the secrets and show the lock screen. Done before anything else here. -/
  lock : Bool
  /-- Make the panel dark. -/
  blank : Bool
  /-- Light the panel and draw the screen as it now is. -/
  wake : Bool
  /-- Pass the press or tap on to the screens. -/
  deliver : Bool
  deriving Repr, Inhabited

/-- Whether an unlocked signer has been left alone long enough to lock. -/
def lockDue (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) : Bool :=
  unlocked && now - s.lastPerson ≥ cfg.lockTicks

/-- One input at time `now`. -/
def step (cfg : Config) (s : State) (unlocked : Bool) (now : Nat) (i : Input) : Decision :=
  let lock := lockDue cfg s unlocked now
  let lastPerson := if i.isPerson then now else s.lastPerson
  match s.phase, i with
  | .on, .none =>
    if now - s.lastScreen ≥ cfg.screenOffTicks then
      { state := { s with phase := .off }, lock, blank := true, wake := false, deliver := false }
    else
      { state := s, lock, blank := false, wake := false, deliver := false }
  | .on, _ =>
    { state := { phase := .on, lastPerson, lastScreen := now }, lock, blank := false, wake := false,
      deliver := i.isPerson }
  | .off, .none =>
    { state := s, lock, blank := false, wake := false, deliver := false }
  | .off, _ =>
    { state := { phase := .on, lastPerson, lastScreen := now }, lock, blank := false, wake := true,
      deliver := false }

end Kernel.Idle
