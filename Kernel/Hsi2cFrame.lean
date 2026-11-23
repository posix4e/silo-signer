/-! # What an I2C register read is made of, and when a bus may be touched (`Kernel.Hsi2cFrame`)

The Pixel's USB-C port controller and its eUSB2 repeater sit on two I2C buses the bootloader set up and this
signer has no driver for. A regtest image looks at them, and only looks: this file is the part of that which
can be reasoned about without the hardware.

1. **The plan of a read.** Reading `n` bytes of register `reg` of a chip is two transfers: the register's
   number written, then `n` bytes read. `plan` is the only way `Kernel.Hsi2c` builds transfers, and the only
   thing it ever writes to a chip is that one byte, which sets where the chip reads from and changes none of
   its registers.
2. **The guard.** A read of a block whose clock is stopped can hang the phone. `Gates.mayTouch` says whether a
   bus's controller may be read at all, from three words read elsewhere: its two clock gates and the word
   that says which protocol its serial block speaks.

Bits are the vendor kernel's: `cal-if/zuma/cmucal-sfr.c` for the gates, `i2c-exynos5.c` for the rest. -/

namespace Kernel.Hsi2cFrame

/-- One transfer on the bus: bytes written to a chip, or a number of bytes read from it. -/
inductive Xfer where
  | write (chip : UInt8) (bytes : List UInt8) (stop : Bool)
  | read (chip : UInt8) (count : Nat) (stop : Bool)
  deriving Repr, DecidableEq

/-- The most bytes one read returns. The controller's queue holds sixteen. -/
def maxRead : Nat := 8

/-- A count of bytes the controller can be asked for: at least one, at most `maxRead`. -/
def clampCount (n : Nat) : Nat := max 1 (min n maxRead)

/-- Reading `n` bytes of register `reg` of `chip`. -/
def plan (chip reg : UInt8) (n : Nat) : List Xfer :=
  [.write chip [reg] false, .read chip (clampCount n) true]

/-- The bytes a transfer puts on the bus after the chip's address. -/
def Xfer.written : Xfer → List UInt8
  | .write _ bytes _ => bytes
  | .read .. => []

/-! ## The guard -/

/-- Whether a clock gate's control word says its clock is running and will stay so: the gate is open
(`CG_VAL`, bit 21) and the hardware may not close it by itself (`ENABLE_AUTOMATIC_CLKGATING`, bit 28). -/
def running (gate : UInt32) : Bool :=
  (gate &&& 0x00200000) != 0 && (gate &&& 0x10000000) == 0

/-- What is read before a bus's controller is: the gates of its two clocks, and the protocol word. -/
structure Gates where
  ipclk : UInt32
  pclk : UInt32
  mode : UInt32
  deriving Repr, Inhabited

/-- The protocol word of a serial block that speaks I2C (`USI_I2C_SW_CONF`). -/
def modeI2c : UInt32 := 4

/-- Why a bus was left alone, or what went wrong on it. The numbers are what the screen shows. -/
inductive Refusal where
  | ipclkGated      -- 1
  | pclkGated       -- 2
  | notI2c          -- 3
  | inReset         -- 4
  | writeTimeout    -- 5
  | noAnswer        -- 6
  | readTimeout     -- 7
  deriving Repr, DecidableEq, Inhabited

def Refusal.code : Refusal → UInt32
  | .ipclkGated => 1
  | .pclkGated => 2
  | .notI2c => 3
  | .inReset => 4
  | .writeTimeout => 5
  | .noAnswer => 6
  | .readTimeout => 7

/-- Whether the controller may be read, and if not, why and the word that says so. -/
def Gates.verdict (g : Gates) : Except (Refusal × UInt32) Unit :=
  if !running g.ipclk then .error (.ipclkGated, g.ipclk)
  else if !running g.pclk then .error (.pclkGated, g.pclk)
  else if (g.mode &&& 7) != modeI2c then .error (.notI2c, g.mode)
  else .ok ()

def Gates.mayTouch (g : Gates) : Bool :=
  match g.verdict with
  | .ok () => true
  | .error _ => false

/-! ## The controller's words for one transfer -/

/-- The address register with `chip` as the chip to talk to: bits 19:10, and the master's own code 7 in
bits 31:24, as the vendor's driver sets outside high-speed mode. -/
def addrWord (old : UInt32) (chip : UInt8) : UInt32 :=
  (old &&& (0x00F00000 : UInt32)) ||| (0x07000000 : UInt32) ||| ((chip.toUInt32 &&& (0x7F : UInt32)) <<< 10)

/-- The automatic-transfer register for a transfer of `len` bytes, not yet started: the length in bits
15:0, bit 16 for a read, bit 17 to end with a stop. -/
def autoConf (old : UInt32) (len : Nat) (read stop : Bool) : UInt32 :=
  (old &&& (0x7FFC0000 : UInt32)) ||| (len.toUInt32 &&& (0xFFFF : UInt32))
    ||| (if read then (0x00010000 : UInt32) else 0) ||| (if stop then (0x00020000 : UInt32) else 0)

/-- The bit that starts it (`HSI2C_MASTER_RUN`). -/
def runBit : UInt32 := 0x80000000

/-- Both queues on, each signalling at `len` bytes. -/
def fifoCtl (len : Nat) : UInt32 :=
  (3 : UInt32) ||| ((len.toUInt32 &&& (0x7F : UInt32)) <<< 4) ||| ((len.toUInt32 &&& (0x7F : UInt32)) <<< 16)

/-- The control register for a transfer: master, with the receive channel on for a read and the transmit
channel on for a write, and never both. -/
def ctlWord (old : UInt32) (read noLoseArbitration : Bool) : UInt32 :=
  ((old &&& ~~~(0xC0 : UInt32)) ||| (0x08 : UInt32) ||| (if read then (0x40 : UInt32) else 0x80))
    ||| (if noLoseArbitration then (0x00400000 : UInt32) else 0)

end Kernel.Hsi2cFrame
