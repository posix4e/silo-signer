import Kernel.Hw
import Kernel.Hsi2c
import Kernel.UsbChips
import Kernel.KomodoTouch

/-! # One look at the Pixel's USB-C port controller, its eUSB2 repeater and their supply (`Kernel.KomodoChips`)

For regtest images. The port controller (`max77759tcpc`) answers at `0x25` on one bus, the repeater
(`samsung,eusb-repeater`) at `0x3E` on another, and both hang off one regulator of the main PMIC, LDO19M,
which also pulls up the port controller's bus.

Everything here reads. The registers are `Kernel.UsbChips`'s lists; the buses are opened through
`Kernel.Hsi2c`'s guard and their pins put back afterwards; the regulator's control byte is asked of the
power-management firmware the way `Kernel.KomodoTouch` asks for the touch controller's supplies, without
the request that changes one. -/

namespace Kernel.KomodoChips

open Kernel
open Kernel.Hsi2cFrame

def tcpcAddr : UInt8 := 0x25
def repeaterAddr : UInt8 := 0x3E

/-- LDO19M's control register on the PMIC's regulator page (`S2MPG14_PM_L19M_CTRL`). -/
def regLdo19m : UInt32 := 0x3D

/-- The register windows a look needs. -/
def windows : List (UInt64 × UInt64) :=
  Hsi2c.tcpcBus.windows ++ Hsi2c.repeaterBus.windows

/-- The registers of `regs` of the chip at `addr` on `bus`, in order. `say` is told what is about to be
touched before each step that has not been taken on this phone before, so that if one of them stops the
phone its screen says which. -/
def readChip (bus : Hsi2c.Bus) (addr : UInt8) (regs : List (UInt8 × Nat)) (name : String)
    (say : String → BaseIO Unit) : BaseIO UsbChips.Chip := do
  say s!"{name}: CLOCK GATES"
  match (← bus.gates).verdict with
  | .error (why, word) => return { err := why.code, word }
  | .ok () => pure ()
  say s!"{name}: CONTROLLER"
  match ← bus.open with
  | .error (why, word) => return { err := why.code, word }
  | .ok o =>
    say s!"{name}: CHIP"
    let mut bytes : List UInt8 := []
    let mut chip : UsbChips.Chip := {}
    for (reg, n) in regs do
      match ← o.readReg addr reg n with
      | .ok got => bytes := bytes ++ got.toList
      | .error (why, word) =>
        chip := { err := why.code, word }
        break
    o.close
    return { chip with bytes }

/-- The regulator's control byte, or `0xFFFFFFFF`. -/
def readLdo (hasPmic : Bool) : BaseIO UInt32 := do
  if !hasPmic then return 0xFFFFFFFF
  let some ch ← KomodoTouch.findChannel | return 0xFFFFFFFF
  match ← ch.pmicRead 61 regLdo19m with
  | some v => return v &&& 0xFF
  | none => return 0xFFFFFFFF

/-- One look. `hasPmic` is whether the firmware's mailbox is within this image's windows. -/
def sample (ticks : Nat) (hasPmic : Bool) (say : String → BaseIO Unit) : BaseIO UsbChips.Sample := do
  let tcpc ← readChip Hsi2c.tcpcBus tcpcAddr UsbChips.tcpcRegs "TCPC" say
  let repeater ← readChip Hsi2c.repeaterBus repeaterAddr UsbChips.repeaterRegs "REPEATER" say
  say "SUPPLY"
  let ldo ← readLdo hasPmic
  return { ticks, tcpc, repeater, ldo }

end Kernel.KomodoChips
