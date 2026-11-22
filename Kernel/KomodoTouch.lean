import Kernel.Hw
import Kernel.Touch

/-! # The Pixel 9 Pro XL's touchscreen, polled (`Kernel.KomodoTouch`)

The panel's touch controller is a Synaptics S3908 speaking TouchComm over SPI. Three things stand between
this signer and a finger's position, and each is done here with register reads and writes only, no
interrupts:

1. **Power.** The controller's two supplies are LDOs of the main PMIC (S2MPG14): LDO25M, 1.8 V, and LDO4M,
   3.3 V. The bootloader leaves them programmed to those voltages and switched off. Only the
   power-management firmware can reach the PMIC, so the request to switch them on goes through its mailbox
   and the queues in its shared memory. This signer sets the enable bit of each and nothing else, and only
   after reading back that the voltage programmed is the one expected.
2. **The bus.** The controller is on `spi_20` (USI2 of the HSI0 block, the block USB is in). The block is
   put in SPI mode, and its clock is taken from the 24 MHz crystal, which gives 6 MHz on the wire.
3. **The conversation.** A message is `A5`, a code and a 16-bit length; its payload is read in a second
   cycle as `A5 03`, the payload and `5A`. The controller identifies itself after reset, says how large the
   panel is, and states the layout of its touch reports, which is checked against the one
   `Kernel.Touch.parseReport` reads.

Addresses and bits are from the Pixel's kernel sources (`zumapro-usi.dtsi`, `zuma-caimito-common-touch.dtsi`,
`pinctrl-gs.c`, `spi-s3c64xx.c`, `cal-if/zuma/cmucal-sfr.c`, `acpm_ipc.c`, `acpm_mfd.c`,
`s2mpg14-register.h`, `syna_gtd/`), and every one of them was first tried from a host over the cable on a
Pixel 9 Pro XL. The queue addresses are not constants: they are read from the firmware's own table, and
checked to lie inside its shared memory before they are used.

If any step fails the signer has no touchscreen and says why; the buttons work as before. -/

namespace Kernel.KomodoTouch

open Kernel

/-! ## Addresses -/

def spiBase : UInt64 := 0x111D0000
def sysregUsiConf : UInt64 := 0x1102101C      -- sysreg_hsi0 + 0x101C: which protocol USI2 speaks
def cmuMuxUsi2 : UInt64 := 0x1100101C         -- cmu_hsi0: USI2's clock, 0 = the shared PERI clock, 1 = the crystal
def gppBase : UInt64 := 0x10840020            -- pinctrl_11, bank gpp1: pin 1 is the controller's reset, active low
def gpnBase : UInt64 := 0x15060000            -- pinctrl_1, bank gpn0: pin 0 is its interrupt line, active low
def mailboxBase : UInt64 := 0x15110000
def sramBase : UInt64 := 0x15700000
def sramSize : UInt64 := 0x58000

def regChCfg : UInt64 := spiBase + 0x00
def regModeCfg : UInt64 := spiBase + 0x08
def regSlaveSel : UInt64 := spiBase + 0x0C
def regIntEn : UInt64 := spiBase + 0x10
def regStatus : UInt64 := spiBase + 0x14
def regTxData : UInt64 := spiBase + 0x18
def regRxData : UInt64 := spiBase + 0x1C
def regPacketCnt : UInt64 := spiBase + 0x20
def regPendingClr : UInt64 := spiBase + 0x24
def regSwapCfg : UInt64 := spiBase + 0x28
def regFbClk : UInt64 := spiBase + 0x2C
def regUsiCon : UInt64 := spiBase + 0xC4

/-- The register windows this driver needs. Without all of them it does not start. -/
def windows : List (UInt64 × UInt64) :=
  [(spiBase, 0x100), (sysregUsiConf, 4), (cmuMuxUsi2, 4), (gppBase, 0x10), (gpnBase, 0x10),
   (mailboxBase, 0x50), (sramBase, sramSize)]

/-- Waits. The counter runs at 24.576 MHz on this phone: about 25 ticks a microsecond. -/
def delayUs (us : UInt64) : BaseIO Unit := do
  let t0 ← Hw.ticks
  let need := us * 25
  for _ in [0:4000000] do
    let t1 ← Hw.ticks
    if t1 - t0 ≥ need then break
    Hw.pause

/-! ## The PMIC, through the power-management firmware's mailbox -/

/-- The firmware's queues for one channel, as addresses. The names are the firmware's: what the AP sends
goes into its `rx` queue, and its answers come back in its `tx` queue. -/
structure Channel where
  rxRear : UInt64
  rxFront : UInt64
  rxBase : UInt64
  txRear : UInt64
  txFront : UInt64
  txBase : UInt64
  qLen : UInt32
  deriving Repr, Inhabited

def pmicChannel : UInt32 := 2

private def inSram (offset : UInt32) (bytes : UInt64) : Bool :=
  offset.toUInt64 % 4 == 0 && offset.toUInt64 + bytes ≤ sramSize

/-- Finds the main PMIC's channel in the firmware's table, and refuses one whose queues are not sixteen
bytes an element, or do not lie inside the shared memory. -/
def findChannel : BaseIO (Option Channel) := do
  let table ← Hw.read32 (sramBase + 0xA000 + 8)
  let count ← Hw.read32 (sramBase + 0xA000 + 12)
  if count == 0 || count > 64 || !inSram table (72 * count.toUInt64) then return none
  for i in [0:count.toNat] do
    let e := sramBase + table.toUInt64 + 72 * i.toUInt64
    if (← Hw.read32 e) == pmicChannel then
      let rxRear ← Hw.read32 (e + 16)
      let rxFront ← Hw.read32 (e + 20)
      let rxBase ← Hw.read32 (e + 24)
      let txRear ← Hw.read32 (e + 40)
      let txFront ← Hw.read32 (e + 44)
      let txBase ← Hw.read32 (e + 48)
      let qLen ← Hw.read32 (e + 52)
      let elem ← Hw.read32 (e + 56)
      if elem != 16 || qLen < 2 || qLen > 63 then return none
      let queue := 16 * qLen.toUInt64
      if !(inSram rxRear 4 && inSram rxFront 4 && inSram txRear 4 && inSram txFront 4
           && inSram rxBase queue && inSram txBase queue) then return none
      return some {
        rxRear := sramBase + rxRear.toUInt64, rxFront := sramBase + rxFront.toUInt64,
        rxBase := sramBase + rxBase.toUInt64, txRear := sramBase + txRear.toUInt64,
        txFront := sramBase + txFront.toUInt64, txBase := sramBase + txBase.toUInt64, qLen }
  return none

/-- One request to the firmware and the second word of its answer, which carries the result. `seq` is 1 to
63 and tells this request's answer from any other's. -/
def Channel.ask (c : Channel) (seq : UInt32) (cmd0 cmd1 : UInt32) : BaseIO (Option UInt32) := do
  let front ← Hw.read32 c.rxFront
  let rear ← Hw.read32 c.rxRear
  if front ≥ c.qLen || (front + 1) % c.qLen == rear then return none
  let slot := c.rxBase + 16 * front.toUInt64
  Hw.write32 slot (cmd0 ||| ((seq &&& 0x3F) <<< 16))
  Hw.write32 (slot + 4) cmd1
  Hw.write32 (slot + 8) 0
  Hw.write32 (slot + 12) 0
  Hw.write32 c.rxFront ((front + 1) % c.qLen)
  Hw.write32 (mailboxBase + 0x40) ((1 : UInt32) <<< pmicChannel)        -- ring the firmware
  for _ in [0:200] do
    delayUs 500
    let tRear ← Hw.read32 c.txRear
    let tFront ← Hw.read32 c.txFront
    if tRear < c.qLen && tFront < c.qLen then
      let mut i := tRear
      for _ in [0:c.qLen.toNat] do
        if i == tFront then break
        let at_ := c.txBase + 16 * i.toUInt64
        if (((← Hw.read32 at_) >>> 16) &&& 0x3F) == (seq &&& 0x3F) then
          let answer ← Hw.read32 (at_ + 4)
          Hw.write32 c.txRear tFront
          Hw.write32 (mailboxBase + 0x24) ((1 : UInt32) <<< pmicChannel)  -- and take its answer as read
          return some answer
        i := (i + 1) % c.qLen
  return none

/-- A register of the PMIC's regulator page. -/
def Channel.pmicRead (c : Channel) (seq : UInt32) (reg : UInt32) : BaseIO (Option UInt32) := do
  match ← c.ask seq (0x0100 ||| reg) 0 with
  | some answer => if answer >>> 24 == 0 then return some ((answer >>> 8) &&& 0xFF) else return none
  | none => return none

/-- Changes the bits of `mask` in one of those registers to those of `value`. -/
def Channel.pmicUpdate (c : Channel) (seq : UInt32) (reg value mask : UInt32) : BaseIO Bool := do
  match ← c.ask seq (0x0100 ||| reg) ((2 : UInt32) ||| (value <<< 8) ||| (mask <<< 16)) with
  | some answer => return answer >>> 24 == 0
  | none => return false

def regLdo4m : UInt32 := 0x2E     -- the controller's 3.3 V
def regLdo25m : UInt32 := 0x43    -- and its 1.8 V
def selLdo4m : UInt32 := 0x3C     -- 1.8 V + 60 × 25 mV
def selLdo25m : UInt32 := 0x2C    -- 0.7 V + 44 × 25 mV

/-- Switches one supply on, if it is programmed to the voltage expected. The voltage is never written. -/
def Channel.supplyOn (c : Channel) (seq : UInt32) (reg selector : UInt32) : BaseIO (Except String Unit) := do
  match ← c.pmicRead seq reg with
  | none => return .error "PMIC READ FAILED"
  | some v =>
    if (v &&& 0x3F) != selector then return .error "SUPPLY NOT AT ITS VOLTAGE"
    if (v &&& 0x80) != 0 then return .ok ()
    if ← c.pmicUpdate (seq + 1) reg 0x80 0x80 then return .ok () else return .error "PMIC WRITE FAILED"

/-! ## The bus -/

def spiInit : BaseIO Unit := do
  Hw.write32 sysregUsiConf 2                    -- USI2 speaks SPI
  Hw.write32 regUsiCon 0                        -- and comes out of reset
  delayUs 100
  Hw.write32 cmuMuxUsi2 1                       -- clocked from the crystal
  delayUs 100
  Hw.write32 regSlaveSel 1
  Hw.write32 regIntEn 0
  Hw.write32 regChCfg 0
  Hw.write32 regModeCfg 0
  Hw.write32 regPacketCnt 0
  Hw.write32 regPendingClr 0x1E
  Hw.write32 regPendingClr 0
  Hw.write32 regSwapCfg 0
  Hw.write32 regFbClk 0
  Hw.write32 regChCfg 0x20
  delayUs 50
  Hw.write32 regChCfg 0
  Hw.write32 regModeCfg 0x1FF80000

/-- The most bytes one run moves: the controller's FIFOs hold 64. -/
def chunk : Nat := 60

/-- Clocks `tx` out and as many bytes in, with chip select low; it stays low afterwards if `hold`. -/
def spiXfer (tx : ByteArray) (hold : Bool) : BaseIO (Option ByteArray) := do
  let n := tx.size
  if n == 0 || n > chunk then return none
  Hw.write32 regChCfg 0x20                      -- empty both FIFOs
  delayUs 20
  Hw.write32 regChCfg 0
  Hw.write32 regSlaveSel 0
  delayUs 5
  Hw.write32 regPacketCnt (n.toUInt32 ||| 0x10000)
  Hw.write32 regChCfg 3
  for b in tx do
    Hw.write32 regTxData b.toUInt32
  let mut arrived := false
  for _ in [0:400] do
    let status ← Hw.read32 regStatus
    if ((status >>> 15) &&& 0x7F) ≥ n.toUInt32 then
      arrived := true
      break
    delayUs 10
  let mut rx := ByteArray.empty
  if arrived then
    for _ in [0:n] do
      rx := rx.push (← Hw.read32 regRxData).toUInt8
  Hw.write32 regChCfg 0
  Hw.write32 regPacketCnt 0
  if !hold || !arrived then Hw.write32 regSlaveSel 1
  return if arrived then some rx else none

/-- Reads `n` bytes in one cycle of chip select. -/
def spiRead (n : Nat) : BaseIO (Option ByteArray) := do
  let mut out := ByteArray.empty
  let mut left := n
  for _ in [0:n / chunk + 1] do
    if left == 0 then break
    let k := min chunk left
    match ← spiXfer (ByteArray.mk (Array.replicate k 0)) (left > k) with
    | none => return none
    | some rx => out := out ++ rx
    left := left - k
  return some out

/-! ## The controller -/

def resetLow : BaseIO Unit := do
  let dat ← Hw.read32 (gppBase + 4)
  Hw.write32 (gppBase + 4) (dat &&& ~~~(2 : UInt32))
  let con ← Hw.read32 gppBase
  Hw.write32 gppBase ((con &&& ~~~(0xF0 : UInt32)) ||| 0x10)     -- pin 1 an output
  let pud ← Hw.read32 (gpnBase + 8)
  Hw.write32 (gpnBase + 8) ((pud &&& ~~~(0xF : UInt32)) ||| 3)   -- the interrupt line pulled up

def resetHigh : BaseIO Unit := do
  let dat ← Hw.read32 (gppBase + 4)
  Hw.write32 (gppBase + 4) (dat ||| 2)

/-- Whether the controller has something to say. -/
def waiting : BaseIO Bool := do
  return ((← Hw.read32 (gpnBase + 4)) &&& 1) == 0

/-- The longest payload believed: ten objects are 131 bytes, and the controller's own limit is 256. -/
def maxPayload : Nat := 512

/-- One message: its code and its payload. -/
def readMessage : BaseIO (Option (UInt8 × ByteArray)) := do
  let some h ← spiRead 4 | return none
  if h.get! 0 != 0xA5 then return none
  let n := (h.get! 2).toNat ||| ((h.get! 3).toNat <<< 8)
  if n == 0 then return some (h.get! 1, ByteArray.empty)
  if n > maxPayload then return none
  delayUs 100
  let some body ← spiRead (n + 3) | return none
  if body.get! 0 != 0xA5 || body.get! 1 != 0x03 || body.get! (n + 2) != 0x5A then return none
  return some (h.get! 1, body.extract 2 (n + 2))

/-- Sends a command with no payload and returns its answer: the first message that is a status and neither
"idle" nor "busy". Reports that arrive meanwhile are dropped. -/
def command (cmd : UInt8) : BaseIO (Option (UInt8 × ByteArray)) := do
  for _ in [0:8] do
    if !(← waiting) then break
    let _ ← readMessage
  let some _ ← spiXfer (ByteArray.mk #[cmd, 0, 0]) false | return none
  for _ in [0:400] do
    delayUs 1000
    if ← waiting then
      match ← readMessage with
      | some (code, payload) => if code < 0x10 && code != 0 && code != 2 then return some (code, payload)
      | none => pure ()
  return none

/-- The layout `Kernel.Touch.parseReport` reads, as the controller states it: gesture, three fields this
signer skips, the number of objects, then for each object its index and classification, x, y, pressure,
two widths and three more bytes. -/
def expectedLayout : ByteArray := ByteArray.mk #[
  0x10, 0x08, 0x1B, 0x38, 0x1E, 0x08, 0x17, 0x08, 0x18, 0x08, 0x04, 0x01,
  0x06, 0x04, 0x07, 0x04, 0x08, 0x10, 0x09, 0x10, 0x0A, 0x10, 0x0B, 0x08, 0x0C, 0x08,
  0xD2, 0x08, 0xD3, 0x08, 0xD1, 0x08, 0x03, 0x00]

/-- A touchscreen that answered: the extent of its panel, and the touch in progress. -/
structure Device where
  maxX : Nat
  maxY : Nat
  tap : Touch.TapState := {}
  deriving Repr, Inhabited

/-- Powers the controller, resets it and asks it what it is. About a third of a second. -/
def init : BaseIO (Except String Device) := do
  spiInit
  resetLow
  let some ch ← findChannel | return .error "TOUCH: NO PMIC CHANNEL"
  match ← ch.supplyOn 1 regLdo25m selLdo25m with
  | .error e => return .error s!"TOUCH 1V8: {e}"
  | .ok () => pure ()
  delayUs 2000
  match ← ch.supplyOn 3 regLdo4m selLdo4m with
  | .error e => return .error s!"TOUCH 3V3: {e}"
  | .ok () => pure ()
  delayUs 200000
  resetHigh
  delayUs 100000
  let some (_, ident) ← command 0x02 | return .error "TOUCH: NO ANSWER"
  if ident.size < 2 || ident.get! 1 != 0x01 then return .error "TOUCH: NOT IN APPLICATION MODE"
  let some (_, app) ← command 0x20 | return .error "TOUCH: NO APP INFO"
  if app.size < 36 then return .error "TOUCH: SHORT APP INFO"
  let maxX := (app.get! 32).toNat ||| ((app.get! 33).toNat <<< 8)
  let maxY := (app.get! 34).toNat ||| ((app.get! 35).toNat <<< 8)
  if maxX == 0 || maxY == 0 then return .error "TOUCH: NO PANEL SIZE"
  let some (_, layout) ← command 0x25 | return .error "TOUCH: NO REPORT LAYOUT"
  if layout.extract 0 expectedLayout.size != expectedLayout then return .error "TOUCH: UNKNOWN REPORT LAYOUT"
  return .ok { maxX, maxY }

/-- Reads at most one message from the controller, and returns the tap it completes, if any, as a place on a
picture `w` by `h` that fills the panel. -/
def Device.poll (d : Device) (w h : Nat) : BaseIO (Device × Option (Nat × Nat)) := do
  if !(← waiting) then return (d, none)
  match ← readMessage with
  | some (0x11, payload) =>
    let (tap', tapped?) := d.tap.step (Touch.parseReport payload)
    return ({ d with tap := tap' }, tapped?.map fun p => Touch.toPicture p d.maxX d.maxY w h)
  | _ => return (d, none)

end Kernel.KomodoTouch
