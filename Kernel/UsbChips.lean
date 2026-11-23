/-! # A short record of the two chips between the USB controller and the connector (`Kernel.UsbChips`)

When the cable is pulled and put back the signer does not come back onto USB, and its controller shows
nothing wrong (`Kernel.UsbLink`). Between the controller and the connector are two chips the bootloader set
up: the USB-C port controller and the eUSB2 repeater. A regtest image reads a few registers of each, keeps
the last few states it has seen, and shows the newest in one line on its screen, since the cable cannot be
asked while it is gone.

This file is the record and the line, pure. Reading the chips is `Kernel.KomodoChips`. -/

namespace Kernel.UsbChips

/-- The port controller's registers that are read, each with its length, in the order kept. The first ten
are the USB Type-C Port Controller Interface's own (Linux `tcpci.h`): vendor id, alert, controller control,
role control, power control, CC status, power status, fault status, extended status. The last three are the
vendor's (`tcpci_max77759_vendor_reg.h`): its two CC status bytes and the switch of the data lines. -/
def tcpcRegs : List (UInt8 × Nat) :=
  [(0x00, 2), (0x10, 2), (0x19, 1), (0x1A, 1), (0x1C, 1), (0x1D, 1), (0x1E, 1), (0x1F, 1), (0x20, 1),
   (0x84, 1), (0x85, 1), (0x93, 1)]

/-- The repeater's, one byte each (the vendor kernel's `eusb_repeater.h`): revision, global configuration
(bit 6: the port is disabled), mode, port configuration, the seven tuning values the device tree sets, the
charger-detection status, and the two interrupt status bytes last. -/
def repeaterRegs : List (UInt8 × Nat) :=
  [(0xB0, 1), (0xB2, 1), (0x50, 1), (0x60, 1), (0x70, 1), (0x71, 1), (0x72, 1), (0x73, 1), (0x77, 1),
   (0x78, 1), (0x79, 1), (0xB7, 1), (0xA3, 1), (0xA4, 1)]

/-- The tuning values the bootloader's device tree gives for registers `70 71 72 73 77 78 79`. -/
def expectedTunes : List UInt8 := [0x7C, 0x3C, 0x92, 0x83, 0x00, 0x0B, 0x60]

/-- What was read of one chip. `err` is 0 when all of it was read; otherwise it is the reason's number
(`Kernel.Hsi2cFrame.Refusal.code`), `word` is the register word that goes with the reason, and `bytes` is
what was read before it. -/
structure Chip where
  err : UInt32 := 0
  word : UInt32 := 0
  bytes : List UInt8 := []
  deriving Inhabited, DecidableEq

/-- One look at both chips and at their supply. `ldo` is the control byte of the regulator that feeds the
repeater and pulls up the port controller's bus, or `0xFFFFFFFF` if it could not be read. -/
structure Sample where
  ticks : Nat := 0
  tcpc : Chip := {}
  repeater : Chip := {}
  ldo : UInt32 := 0xFFFFFFFF
  deriving Inhabited

/-- Whether two looks show the same chips. The time does not count. -/
def Sample.same (a b : Sample) : Bool :=
  a.tcpc == b.tcpc && a.repeater == b.repeater && a.ldo == b.ldo

/-- How many states are kept. -/
def bound : Nat := 32

/-- The record with one more look: newest first. A look that shows the same as the newest one kept is not
added, and the oldest are dropped past `bound`. -/
def note (log : List Sample) (s : Sample) : List Sample :=
  match log with
  | [] => [s]
  | last :: _ => if last.same s then log else s :: log.take (bound - 1)

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (55 + n)

def hex2 (b : UInt8) : String :=
  String.ofList [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

def hex8 (w : UInt32) : String :=
  String.join ((List.range 4).map fun k => hex2 (w >>> (8 * (3 - k)).toUInt32).toUInt8)

private def byteAt (c : Chip) (i : Nat) : String :=
  match c.bytes[i]? with
  | some b => hex2 b
  | none => "--"

/-- Whether the repeater's tuning values are the device tree's. -/
def Sample.tunesMatch (s : Sample) : Bool :=
  (s.repeater.bytes.drop 4).take 7 == expectedTunes

/-- The port controller in the line: CC status, power status, role control and the data switch, or `!`,
the reason's number and its word. -/
def Sample.tcpcText (s : Sample) : String :=
  if s.tcpc.err != 0 then s!"!{s.tcpc.err}:{hex8 s.tcpc.word}"
  else byteAt s.tcpc 7 ++ byteAt s.tcpc 8 ++ byteAt s.tcpc 5 ++ byteAt s.tcpc 13

/-- The repeater in the line: global configuration, mode, port configuration, and whether its tuning is the
device tree's. -/
def Sample.repeaterText (s : Sample) : String :=
  if s.repeater.err != 0 then s!"!{s.repeater.err}:{hex8 s.repeater.word}"
  else byteAt s.repeater 1 ++ byteAt s.repeater 2 ++ byteAt s.repeater 3 ++ (if s.tunesMatch then "t1" else "t0")

/-- The line a regtest image shows: `T` the port controller, `R` the repeater, `P` their supply's control
byte, and how many states have been seen, so that one missed between two looks at the screen is noticed. -/
def Sample.line (s : Sample) (seen : Nat) : String :=
  let p := if s.ldo > 0xFF then "--" else hex2 s.ldo.toUInt8
  s!"T{s.tcpcText} R{s.repeaterText} P{p} #{seen}"

end Kernel.UsbChips
