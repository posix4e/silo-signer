/-! # A short record of what the USB controller has been seen to do (`Kernel.UsbLink`)

When the cable is pulled and put back the signer may not come back onto USB, and the bench cannot ask why:
its questions travel over the same link. So a regtest image keeps the last few states of the link it has
seen, each with the time it was first seen, to be read on its screen or over the cable once that works again.

This file is the record alone, pure. Reading the controller is `Kernel.Dwc3.Device.sample`. -/

namespace Kernel.UsbLink

/-- One look at the link. `dsts` is the controller's status with its frame counter masked off, so that it
changes only when the link's state or speed does. -/
structure Sample where
  ticks : Nat := 0
  dsts : UInt32 := 0
  dctl : UInt32 := 0
  events : Nat := 0
  lastEv : UInt32 := 0
  configured : Bool := false
  gated : Bool := false
  deriving Inhabited

/-- Whether two looks show the same link. The time, and how many events have gone by, do not count: a link
that is carrying frames is not changing. -/
def Sample.same (a b : Sample) : Bool :=
  a.dsts == b.dsts && a.dctl == b.dctl && a.configured == b.configured && a.gated == b.gated

/-- How many states are kept. -/
def bound : Nat := 32

/-- The record with one more look: newest first. A look that shows the same link as the newest one kept is
not added, and the oldest are dropped past `bound`. -/
def note (log : List Sample) (s : Sample) : List Sample :=
  match log with
  | [] => [s]
  | last :: _ => if last.same s then log else s :: log.take (bound - 1)

/-- The link's state, from the controller's status: 0 is on, 3 is suspended, 4 is no host, 5 is waiting. -/
def Sample.linkState (s : Sample) : UInt32 := (s.dsts >>> 18) &&& 0xF

/-- The speed the link came up at: 0 is high speed. -/
def Sample.speed (s : Sample) : UInt32 := s.dsts &&& 0x7

end Kernel.UsbLink
