import Kernel.Hw
import Kernel.Hsi2cFrame

/-! # A polled I2C master that only reads (`Kernel.Hsi2c`)

Two of the Pixel 9 Pro XL's I2C buses, as far as a regtest image needs them to look at the chips between its
USB controller and the connector: the USB-C port controller at `0x25` on `hsi2c@108C0000`, and the eUSB2
repeater at `0x3E` on `hsi2c@10C90000`. Both are Samsung serial blocks (USI v2) in I2C mode, which the
bootloader has used and left.

The one thing this file offers is `Bus.readReg`: some bytes of one register of one chip. Its transfers are
`Kernel.Hsi2cFrame.plan`'s, so the only byte ever written to a chip is a register's number
(`Kernel.Hsi2cFrameProofs.plan_writes_only_the_register_number`).

A read of a block whose clock is stopped can hang the phone, so nothing of a bus's controller is read
before `Bus.gates` has read its two clock gates and its protocol word and `Hsi2cFrame.Gates.verdict` has
passed them, and then only its reset word first. Neither block has a power domain in the bootloader's
device tree: they are always powered.

What is written on the phone's side: the controller's own registers, and the function and pull of the
bus's two pins, which `Bus.close` puts back as they were. The vendor's driver does the same around each
transfer of the port controller's bus, whose pins rest as inputs.

Registers, bits and order are the vendor kernel's `drivers/i2c/busses/i2c-exynos5.c` (its polled automatic
mode), the interrupt bits Linux's `i2c-exynos5.c`; addresses are from the device tree, `cmucal-sfr.c` and
`pinctrl-gs.c`. -/

namespace Kernel.Hsi2c

open Kernel
open Kernel.Hsi2cFrame

/-- One bus: where its controller, its clock gates, its protocol word and its pins are. -/
structure Bus where
  base : UInt64
  gateIpclk : UInt64
  gatePclk : UInt64
  modeReg : UInt64
  /-- The pin bank's first register; its pull register is 8 further on. -/
  pinBank : UInt64
  /-- The first of the bus's two pins in that bank. -/
  firstPin : UInt32
  /-- The pins' function for I2C, and their pull while it is in use. -/
  pinFunction : UInt32
  pinPull : UInt32
  noLoseArbitration : Bool
  deriving Repr, Inhabited

/-- `hsi2c@108C0000`, USI5 of PERIC0: the USB-C port controller's bus. Pins gpp10-0 and gpp10-1. -/
def tcpcBus : Bus where
  base := 0x108C0000
  gateIpclk := 0x10802090
  gatePclk := 0x10802094
  modeReg := 0x10821010
  pinBank := 0x10840140
  firstPin := 0
  pinFunction := 3
  pinPull := 3
  noLoseArbitration := true

/-- `hsi2c@10C90000`, USI9 of PERIC1: the eUSB2 repeater's bus. Pins gpp19-4 and gpp19-5. -/
def repeaterBus : Bus where
  base := 0x10C90000
  gateIpclk := 0x10C02070
  gatePclk := 0x10C02074
  modeReg := 0x10C21004
  pinBank := 0x10C40000
  firstPin := 4
  pinFunction := 2
  pinPull := 0
  noLoseArbitration := false

/-- The register windows a bus needs. -/
def Bus.windows (b : Bus) : List (UInt64 × UInt64) :=
  [(b.base, 0x100), (b.gateIpclk, 4), (b.gatePclk, 4), (b.modeReg, 4), (b.pinBank, 0x10)]

def regCtl : UInt64 := 0x00
def regFifoCtl : UInt64 := 0x04
def regTrailingCtl : UInt64 := 0x08
def regIntEnable : UInt64 := 0x20
def regIntStatus : UInt64 := 0x24
def regFifoStatus : UInt64 := 0x30
def regTxData : UInt64 := 0x34
def regRxData : UInt64 := 0x38
def regConf : UInt64 := 0x40
def regAutoConf : UInt64 := 0x44
def regTimeout : UInt64 := 0x48
def regTimingFs1 : UInt64 := 0x60
def regTimingFs2 : UInt64 := 0x64
def regTimingFs3 : UInt64 := 0x68
def regAddr : UInt64 := 0x70
def regUsiCon : UInt64 := 0xC4

/-- Transfer done; and the four ways it can fail: aborted, no acknowledgement, no chip, timed out. -/
def intDone : UInt32 := 0x080
def intFailed : UInt32 := 0xF00

/-- About 25 ticks a microsecond on this phone. -/
private def ticksPerMs : UInt64 := 24576

/-- The bus's two clock gates and its protocol word. Reads nothing of the controller. -/
def Bus.gates (b : Bus) : BaseIO Gates := do
  let ipclk ← Hw.read32 b.gateIpclk
  let pclk ← Hw.read32 b.gatePclk
  let mode ← Hw.read32 b.modeReg
  return { ipclk, pclk, mode }

/-- The pins as they were found, to be put back. -/
structure Pins where
  con : UInt32
  pud : UInt32
  deriving Repr, Inhabited

private def nibbles (b : Bus) (v : UInt32) : UInt32 :=
  (v <<< (4 * b.firstPin)) ||| (v <<< (4 * (b.firstPin + 1)))

/-- Gives the bus its two pins. -/
def Bus.takePins (b : Bus) : BaseIO Pins := do
  let con ← Hw.read32 b.pinBank
  let pud ← Hw.read32 (b.pinBank + 8)
  let mask := nibbles b 0xF
  let pud' := (pud &&& ~~~mask) ||| nibbles b b.pinPull
  let con' := (con &&& ~~~mask) ||| nibbles b b.pinFunction
  if pud' != pud then Hw.write32 (b.pinBank + 8) pud'
  if con' != con then Hw.write32 b.pinBank con'
  return { con, pud }

def Bus.givePins (b : Bus) (p : Pins) : BaseIO Unit := do
  if (← Hw.read32 b.pinBank) != p.con then Hw.write32 b.pinBank p.con
  if (← Hw.read32 (b.pinBank + 8)) != p.pud then Hw.write32 (b.pinBank + 8) p.pud

/-- Starts the controller over as a master in automatic mode at 400 kHz or slower. The timing is the
vendor's arithmetic for the 200 MHz the device tree gives as the block's clock: a divider of 31, and the
high and start-hold times that go with it. A slower clock makes a slower bus. -/
def Bus.reset (b : Bus) : BaseIO Unit := do
  let ctl ← Hw.read32 (b.base + regCtl)
  Hw.write32 (b.base + regCtl) (ctl ||| 0x80000000)
  let ctl ← Hw.read32 (b.base + regCtl)
  Hw.write32 (b.base + regCtl) (ctl &&& 0x7FFFFFFF)
  let fs3 ← Hw.read32 (b.base + regTimingFs3)
  Hw.write32 (b.base + regTimingFs3) ((fs3 &&& ~~~(0x00FF0000 : UInt32)) ||| (0x001F0000 : UInt32))
  let fs2 ← Hw.read32 (b.base + regTimingFs2)
  Hw.write32 (b.base + regTimingFs2) ((fs2 &&& ~~~(0x000000FF : UInt32)) ||| (0xE0 : UInt32))
  let fs1 ← Hw.read32 (b.base + regTimingFs1)
  Hw.write32 (b.base + regTimingFs1) ((fs1 &&& ~~~(0x00FF0000 : UInt32)) ||| (0x00F00000 : UInt32))
  Hw.write32 (b.base + regIntEnable) 0
  Hw.write32 (b.base + regCtl) 0x08
  Hw.write32 (b.base + regTrailingCtl) 0x00FFFFFF
  let conf ← Hw.read32 (b.base + regConf)
  Hw.write32 (b.base + regConf) ((conf &&& ~~~(0x20000000 : UInt32)) ||| 0x80000000)

/-- A bus that passed the guard, and its pins as they were. -/
structure Open where
  bus : Bus
  pins : Pins
  deriving Repr, Inhabited

/-- Checks that the bus may be touched, takes its pins and starts its controller over. A bus that may not
be touched is not touched: the answer is why, and the word that says so. -/
def Bus.open (b : Bus) : BaseIO (Except (Refusal × UInt32) Open) := do
  match (← b.gates).verdict with
  | .error why => return .error why
  | .ok () =>
    let usiCon ← Hw.read32 (b.base + regUsiCon)
    if (usiCon &&& 1) != 0 then return .error (.inReset, usiCon)
    let pins ← b.takePins
    b.reset
    return .ok { bus := b, pins }

def Open.close (o : Open) : BaseIO Unit := do
  Hw.write32 (o.bus.base + regIntEnable) 0
  o.bus.givePins o.pins

/-- Ends a transfer: nothing left asking for attention. -/
private def quiet (b : Bus) : BaseIO Unit := do
  Hw.write32 (b.base + regIntEnable) 0
  Hw.write32 (b.base + regIntStatus) (← Hw.read32 (b.base + regIntStatus))

/-- One transfer, in the vendor driver's order. Waits at most 20 ms. -/
private def xfer (b : Bus) (x : Xfer) : BaseIO (Except (Refusal × UInt32) ByteArray) := do
  let (chip, len, isRead, stop, bytes) := match x with
    | .write chip bytes stop => (chip, bytes.length, false, stop, bytes)
    | .read chip count stop => (chip, count, true, stop, [])
  let base := b.base
  let timeout ← Hw.read32 (base + regTimeout)
  Hw.write32 (base + regTimeout) (timeout &&& 0x7FFFFFFF)
  Hw.write32 (base + regFifoCtl) (fifoCtl len)
  Hw.write32 (base + regIntStatus) (← Hw.read32 (base + regIntStatus))
  Hw.write32 (base + regAddr) (addrWord (← Hw.read32 (base + regAddr)) chip)
  Hw.write32 (base + regCtl) (ctlWord (← Hw.read32 (base + regCtl)) isRead b.noLoseArbitration)
  Hw.write32 (base + regIntEnable) (intDone ||| intFailed)
  let conf := autoConf (← Hw.read32 (base + regAutoConf)) len isRead stop
  Hw.write32 (base + regAutoConf) conf
  Hw.write32 (base + regAutoConf) (conf ||| runBit)
  for byte in bytes do
    Hw.write32 (base + regTxData) byte.toUInt32
  let t0 ← Hw.ticks
  let mut got := ByteArray.empty
  let mut done := false
  let mut failed : UInt32 := 0
  for _ in [0:2000000] do
    let status ← Hw.read32 (base + regIntStatus)
    if (status &&& intFailed) != 0 then
      failed := status
      break
    let fifo ← Hw.read32 (base + regFifoStatus)
    if isRead then
      if (fifo &&& 0x01000000) == 0 && got.size < len then
        got := got.push (← Hw.read32 (base + regRxData)).toUInt8
      if got.size ≥ len then
        done := true
        break
    else if (status &&& intDone) != 0 && (fifo &&& 0x100) != 0 then
      done := true
      break
    if (← Hw.ticks) - t0 > 20 * ticksPerMs then break
    Hw.pause
  if failed != 0 then
    quiet b
    b.reset
    return .error (.noAnswer, failed)
  if !done then
    let status ← Hw.read32 (base + regIntStatus)
    quiet b
    b.reset
    return .error (if isRead then .readTimeout else .writeTimeout, status)
  quiet b
  return .ok got

/-- `n` bytes (at most `Hsi2cFrame.maxRead`) of register `reg` of the chip at `chip`. -/
def Open.readReg (o : Open) (chip reg : UInt8) (n : Nat) : BaseIO (Except (Refusal × UInt32) ByteArray) := do
  let mut out := ByteArray.empty
  for x in plan chip reg n do
    match ← xfer o.bus x with
    | .error why => return .error why
    | .ok bytes => out := out ++ bytes
  return .ok out

end Kernel.Hsi2c
