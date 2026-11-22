/-! # Touch reports and taps (`Kernel.Touch`)

What the panel's touch controller says, read as taps. Nothing here touches hardware: a report's bytes go in,
and at most one tap comes out, when a finger that went down and stayed put is lifted.

The report's layout is the one the Pixel 9 Pro XL's controller (Synaptics S3908) states for itself in answer
to "get touch report config": eleven bytes, the last of them the number of objects on the glass, then
twelve bytes for each object (its index and classification in one byte, then x, y and pressure as 16-bit
little-endian numbers, and five bytes this signer has no use for). `Kernel.KomodoTouch` checks that the
controller states this layout before it believes a report.

What is proved (`Kernel/TouchProofs.lean`): a finger going down or moving never taps; a tap comes only from a
lift, of a finger that did not move, at the place it went down; and after a lift nothing is held over. -/

namespace Kernel.Touch

/-- A place on the glass, in the controller's own units (tenths of a pixel on this panel). -/
structure Point where
  x : Nat
  y : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- What one report says about the first finger: where it is, or that there is none. -/
inductive Sample where
  | down (p : Point)
  | up
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Bytes before the first object, and bytes an object takes. -/
def headerBytes : Nat := 11
def objectBytes : Nat := 12

/-- Classifications that are a deliberate touch: a finger, a gloved finger, a stylus, a small object. A palm,
a hover, an edge grip and a lift are not. -/
def isTouch (classification : Nat) : Bool :=
  classification == 1 || classification == 2 || classification == 3 || classification == 5

private def u16At (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat ||| ((b.get! (o + 1)).toNat <<< 8)

/-- The first object in a report that is a deliberate touch, if the report holds one whole. -/
def parseReport (p : ByteArray) : Sample := Id.run do
  if p.size < headerBytes then return .up
  let count := (p.get! (headerBytes - 1)).toNat
  for k in [0:count] do
    let o := headerBytes + objectBytes * k
    if o + objectBytes ≤ p.size then
      if isTouch ((p.get! o).toNat >>> 4) then
        return .down { x := u16At p (o + 1), y := u16At p (o + 3) }
  return .up

/-- How far a finger may wander between going down and lifting and still have tapped: 4 mm on this panel
(19 pixels a millimetre, ten units a pixel). -/
def slop : Nat := 760

def far (a b : Point) : Bool :=
  (if a.x ≤ b.x then b.x - a.x else a.x - b.x) > slop ||
  (if a.y ≤ b.y then b.y - a.y else a.y - b.y) > slop

/-- A touch in progress: where it began, and whether it has moved too far to be a tap. -/
structure TapState where
  start? : Option Point := none
  moved : Bool := false
  deriving BEq, DecidableEq, Repr, Inhabited

/-- One report's sample, and the tap it completes, if any. -/
def TapState.step (s : TapState) : Sample → TapState × Option Point
  | .down p =>
    match s.start? with
    | none => ({ start? := some p, moved := false }, none)
    | some a => ({ s with moved := s.moved || far a p }, none)
  | .up =>
    match s.start? with
    | none => ({}, none)
    | some a => ({}, if s.moved then none else some a)

/-- A place on the glass as a place on a picture `w` by `h` that fills the panel, whose own extent is
`maxX + 1` by `maxY + 1` units. -/
def toPicture (p : Point) (maxX maxY w h : Nat) : Nat × Nat :=
  (p.x * w / (maxX + 1), p.y * h / (maxY + 1))

end Kernel.Touch
