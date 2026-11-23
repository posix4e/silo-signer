import Kernel.Hw
import Kernel.Wire
import Kernel.UsbLink

/-! # Pure-Lean Polled Synopsys DWC3 USB-C Device Driver (`Kernel.Dwc3`)

Drives Tensor G4 (`komodo`) Synopsys `DWC3` (`0x11210000`) in USB 2.0 High-Speed Device mode with:
- Zero interrupts, zero threads, zero Linux USB gadget stack, zero filesystem
- Strictly capability-checked MMIO & DMA access via `Kernel.Hw`
- Safe `PMU_ALIVE` power-domain check (`PD_HSI0 @ 0x15462A84`) before touching `DWC3`
- Standard USB 2.0 Device / Configuration / UTF-16LE String descriptors (`VID=0x1209`, `PID=0x4701`)
  exposing one Vendor-Specific interface (`0xFF`) with Bulk-OUT (`0x01`) + Bulk-IN (`0x81`) carrying
  our formally verified CRC-32 `Kernel.Wire` frames!

Descriptor & SETUP packet bounds properties are proved in `Kernel/Dwc3Proofs.lean`. -/

namespace Kernel.Dwc3

open Kernel

/-! ## Synopsys DWC3 & Tensor G4 PMU Register Offsets -/

def dwc3DefaultBase : UInt64 := 0x11210000
def usbBlkconBase : UInt64 := 0x11100000
def usbEusbconBase : UInt64 := 0x11110000
def pmuPdHsi0Status : UInt64 := 0x15462A84
def pmuUsbPhyIso : UInt64 := 0x15463EB0

def blkconLinkCtrl : UInt64 := 0x0004
def blkconLinkClkRst : UInt64 := 0x000C
def blkconUtmiCtrl : UInt64 := 0x0010

def eusbconRstCtrl : UInt64 := 0x0000
def eusbconCmnCtrl : UInt64 := 0x0004
def eusbconPllCfg0 : UInt64 := 0x0008
def eusbconPllCfg1 : UInt64 := 0x000C
def eusbconUtmi : UInt64 := 0x001C
def eusbconTestSe : UInt64 := 0x0020

def regGctl : UInt64 := 0xC110
def regGsnpsId : UInt64 := 0xC120
def regGusb2PhyCfg0 : UInt64 := 0xC200
def regGusb3PipeCtl0 : UInt64 := 0xC2C0
def regGevntAdrLo0 : UInt64 := 0xC400
def regGevntAdrHi0 : UInt64 := 0xC404
def regGevntSiz0 : UInt64 := 0xC408
def regGevntCount0 : UInt64 := 0xC40C

def regDcfg : UInt64 := 0xC700
def regDctl : UInt64 := 0xC704
def regDevten : UInt64 := 0xC708
def regDsts : UInt64 := 0xC70C
def regDalepena : UInt64 := 0xC720

def depCmdPar2 (ep : Nat) : UInt64 := 0xC800 + (ep * 0x10).toUInt64
def depCmdPar1 (ep : Nat) : UInt64 := 0xC804 + (ep * 0x10).toUInt64
def depCmdPar0 (ep : Nat) : UInt64 := 0xC808 + (ep * 0x10).toUInt64
def depCmd (ep : Nat) : UInt64 := 0xC80C + (ep * 0x10).toUInt64

def cmdSetEpCfg : UInt32 := 1
def cmdSetXferRes : UInt32 := 2
def cmdSetStall : UInt32 := 4
def cmdClearStall : UInt32 := 5
def cmdStartXfer : UInt32 := 6
def cmdEndXfer : UInt32 := 8
def cmdStartNewCfg : UInt32 := 9
def cmdAct : UInt32 := (1 : UInt32) <<< 10

def trbCtrlNormal : UInt32 := 1
def trbCtrlSetup : UInt32 := 2
def trbCtrlStatus2 : UInt32 := 3
def trbCtrlStatus3 : UInt32 := 4
def trbCtrlData : UInt32 := 5
def trbHwo : UInt32 := 1
def trbLst : UInt32 := 2
def trbIsp : UInt32 := (1 : UInt32) <<< 10
def trbIoc : UInt32 := (1 : UInt32) <<< 11

/-! ## Pure USB 2.0 Descriptors & SETUP Request Decoder (Formally Verified!) -/

def usbVendorId : UInt16 := 0x1209   -- pid.codes open hardware test VID
def usbProductId : UInt16 := 0x4701  -- on the pid.codes test vendor id

/-- 18-byte USB 2.0 Device Descriptor (`VID=0x1209`, `PID=0x4701`, 64-byte EP0). -/
def deviceDescriptor : ByteArray := ByteArray.mk #[
  18, 0x01,                   -- bLength=18, bDescriptorType=DEVICE
  0x00, 0x02,                 -- bcdUSB = 2.00
  0x00, 0x00, 0x00,           -- Device class/subclass/protocol defined at interface level
  64,                         -- bMaxPacketSize0 = 64
  0x09, 0x12,                 -- idVendor  = 0x1209 (LE)
  0x01, 0x47,                 -- idProduct = 0x4701 (LE)
  0x00, 0x01,                 -- bcdDevice = 1.00
  1, 2, 3,                    -- iManufacturer=1, iProduct=2, iSerialNumber=3
  1                           -- bNumConfigurations = 1
]

/-- 32-byte USB 2.0 Configuration + Vendor Interface (`0xFF`) + Bulk OUT (`0x01`) + Bulk IN (`0x81`). -/
def configDescriptor (bulkMaxPkt : UInt16 := 512) : ByteArray :=
  let mpLo := (bulkMaxPkt &&& 0xff).toUInt8
  let mpHi := ((bulkMaxPkt >>> 8) &&& 0xff).toUInt8
  ByteArray.mk #[
    -- Configuration Descriptor (9 bytes)
    9, 0x02, 32, 0x00,        -- bLength=9, CONFIGURATION, wTotalLength=32
    1, 1, 0,                  -- bNumInterfaces=1, bConfigurationValue=1, iConfiguration=0
    0xC0, 250,                -- bmAttributes=Self-Powered, bMaxPower=500mA
    -- Interface Descriptor (9 bytes)
    9, 0x04, 0, 0, 2,         -- bLength=9, INTERFACE, iface=0, alt=0, numEPs=2
    0xFF, 0x47, 0x01, 0,      -- Vendor-Specific class 0xFF, sub 0x47, proto 0x01
    -- Endpoint 1 OUT Bulk (7 bytes)
    7, 0x05, 0x01, 0x02,      -- bLength=7, ENDPOINT, addr=0x01 (OUT), attr=Bulk
    mpLo, mpHi, 0,            -- wMaxPacketSize, bInterval=0
    -- Endpoint 1 IN Bulk (7 bytes)
    7, 0x05, 0x81, 0x02,      -- bLength=7, ENDPOINT, addr=0x81 (IN), attr=Bulk
    mpLo, mpHi, 0             -- wMaxPacketSize, bInterval=0
  ]

/-- Builds a standard UTF-16LE USB String Descriptor from ASCII text. -/
def asciiStringDescriptor (s : String) : ByteArray := Id.run do
  let bs := s.toUTF8
  let maxChars := min bs.size 60
  let totalLen := 2 + maxChars * 2
  let mut out := ByteArray.mk #[totalLen.toUInt8, 0x03]
  for i in [0:maxChars] do
    out := out.push (bs.get! i) |>.push 0x00
  return out

def stringDescriptor (idx : UInt8) : Option ByteArray :=
  match idx.toNat with
  | 0 => some (ByteArray.mk #[4, 0x03, 0x09, 0x04]) -- English (US)
  | 1 => some (asciiStringDescriptor "Silo Tricorder")
  | 2 => some (asciiStringDescriptor "Tricorder Bare-Metal Signer")
  | 3 => some (asciiStringDescriptor "4701-KOMODO")
  | _ => none

/-- Decoded 8-byte USB Control SETUP packet. -/
structure SetupPacket where
  bmRequestType : UInt8
  bRequest : UInt8
  wValue : UInt16
  wIndex : UInt16
  wLength : UInt16
  deriving BEq, Repr, Inhabited

def decodeSetup (b : ByteArray) : Option SetupPacket :=
  if b.size < 8 then none
  else
    let wValue := (b.get! 2).toUInt16 ||| ((b.get! 3).toUInt16 <<< 8)
    let wIndex := (b.get! 4).toUInt16 ||| ((b.get! 5).toUInt16 <<< 8)
    let wLength := (b.get! 6).toUInt16 ||| ((b.get! 7).toUInt16 <<< 8)
    some { bmRequestType := b.get! 0, bRequest := b.get! 1, wValue, wIndex, wLength }

/-- Pure response action for a standard USB EP0 SETUP packet. -/
inductive SetupAction where
  | sendData (data : ByteArray)
  | setAddress (addr : UInt8)
  | setConfiguration (cfg : UInt8)
  | ackZero
  | stall
  deriving BEq

/-- Clamps an outgoing EP0 descriptor reply strictly to the host's requested `wLength`. -/
def clampToWLength (data : ByteArray) (wLength : UInt16) : ByteArray :=
  let lim := min data.size wLength.toNat
  data.extract 0 lim

/-- Pure USB 2.0 Chapter 9 standard SETUP request dispatcher. -/
def handleStandardSetup (req : SetupPacket) (bulkMaxPkt : UInt16 := 512) : SetupAction :=
  match req.bRequest.toNat with
  | 0 => -- GET_STATUS
    .sendData (clampToWLength (ByteArray.mk #[0x01, 0x00]) req.wLength) -- self-powered
  | 1 | 3 => -- CLEAR_FEATURE / SET_FEATURE
    .ackZero
  | 5 => -- SET_ADDRESS
    .setAddress (req.wValue &&& 0x7f).toUInt8
  | 6 => -- GET_DESCRIPTOR
    let descType := (req.wValue >>> 8).toUInt8
    let descIdx := (req.wValue &&& 0xff).toUInt8
    match descType.toNat with
    | 1 => .sendData (clampToWLength deviceDescriptor req.wLength)
    | 2 => .sendData (clampToWLength (configDescriptor bulkMaxPkt) req.wLength)
    | 3 =>
      match stringDescriptor descIdx with
      | some sd => .sendData (clampToWLength sd req.wLength)
      | none => .stall
    | 6 => -- DEVICE_QUALIFIER (USB 2.0)
      .sendData (clampToWLength (ByteArray.mk #[10, 0x06, 0x00, 0x02, 0, 0, 0, 64, 1, 0]) req.wLength)
    | _ => .stall
  | 8 => -- GET_CONFIGURATION
    .sendData (clampToWLength (ByteArray.mk #[1]) req.wLength)
  | 9 => -- SET_CONFIGURATION
    .setConfiguration (req.wValue &&& 0xff).toUInt8
  | 10 => -- GET_INTERFACE
    .sendData (clampToWLength (ByteArray.mk #[0]) req.wLength)
  | 11 => -- SET_INTERFACE
    .ackZero
  | _ => .stall

/-! ## Polled Synopsys DWC3 Hardware State Machine -/

private def pushLe32 (b : ByteArray) (v : UInt32) : ByteArray :=
  b.push (v &&& 0xff).toUInt8
   |>.push ((v >>> 8) &&& 0xff).toUInt8
   |>.push ((v >>> 16) &&& 0xff).toUInt8
   |>.push ((v >>> 24) &&& 0xff).toUInt8

private def readLe32 (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 4 ≤ b.size then
    (b.get! off).toUInt32 |||
    ((b.get! (off + 1)).toUInt32 <<< 8) |||
    ((b.get! (off + 2)).toUInt32 <<< 16) |||
    ((b.get! (off + 3)).toUInt32 <<< 24)
  else 0

private def makeTrb (bufAddr : UInt64) (bufSize : UInt32) (trbType : UInt32) : ByteArray :=
  let lo := bufAddr.toUInt32
  let hi := (bufAddr >>> 32).toUInt32
  let siz := bufSize &&& 0x00FFFFFF
  let ctrl := trbHwo ||| trbLst ||| trbIsp ||| trbIoc ||| ((trbType &&& 0x3f) <<< 4)
  pushLe32 (pushLe32 (pushLe32 (pushLe32 ByteArray.empty lo) hi) siz) ctrl

private def sendEpCmd (base : UInt64) (ep : Nat) (cmd p0 p1 p2 : UInt32) : BaseIO UInt32 := do
  Hw.write32 (base + depCmdPar2 ep) p2
  Hw.write32 (base + depCmdPar1 ep) p1
  Hw.write32 (base + depCmdPar0 ep) p0
  Hw.write32 (base + depCmd ep) (cmd ||| cmdAct)
  for _ in [0:200000] do
    let r ← Hw.read32 (base + depCmd ep)
    if (r &&& cmdAct) == 0 then
      return r
    Hw.pause
  return 0xFFFFFFFF

private def startTrb (base : UInt64) (ep : Nat) (trbAddr bufAddr : UInt64)
    (bufSize : UInt32) (trbType : UInt32) : BaseIO UInt32 := do
  Hw.store trbAddr (makeTrb bufAddr bufSize trbType)
  let r ← sendEpCmd base ep cmdStartXfer (trbAddr >>> 32).toUInt32 trbAddr.toUInt32 0
  return (r >>> 16) &&& 0x7f -- XferRscIdx

inductive Ep0Phase where
  | setup
  | dataIn
  | waitStatusOut
  | statusOut
  | waitStatusIn
  | statusIn
  deriving BEq, Repr, Inhabited

structure Device where
  base : UInt64
  snpsId : UInt32
  evBuf : UInt64
  evSize : Nat := 4096
  evPos : Nat := 0
  trbPage : UInt64      -- +0: EP0-OUT TRB, +64: EP0-IN TRB, +128: Bulk-OUT TRB, +192: Bulk-IN TRB
  setupBuf : UInt64     -- 64B SETUP buffer
  ep0DataBuf : UInt64   -- 512B EP0 IN data buffer
  bulkOutBuf : UInt64   -- 4096B Bulk-OUT RX buffer
  bulkInBuf : UInt64    -- 4096B Bulk-IN TX buffer
  ep0Phase : Ep0Phase := .setup
  ep0OutRsc : UInt32 := 0
  ep0InRsc : UInt32 := 0
  ep0OutActive : Bool := false
  ep0InActive : Bool := false
  bulkMaxPkt : UInt16 := 512
  configured : Bool := false
  bulkOutArmed : Bool := false
  bulkOutReqLen : Nat := 4096
  bulkInBusy : Bool := false
  evSeen : Nat := 0
  lastEv : UInt32 := 0
  lastSetupReq : UInt8 := 0
  lastSetupVal : UInt16 := 0
  hasPmu : Bool := false
  hasBlkcon : Bool := false
  hasEusbcon : Bool := false
  clkGated : Bool := false
  rxAccum : ByteArray := ByteArray.empty
  deriving Inhabited

private def Device.ep0OutTrb (d : Device) : UInt64 := d.trbPage
private def Device.ep0InTrb (d : Device) : UInt64 := d.trbPage + 64
private def Device.bulkOutTrb (d : Device) : UInt64 := d.trbPage + 128
private def Device.bulkInTrb (d : Device) : UInt64 := d.trbPage + 192

private def endXfer (base : UInt64) (ep : Nat) (rsc : UInt32) : BaseIO Unit := do
  -- DEPENDXFER: ForceRM (bit 11) + XferRscIdx ([22:16]), no IOC
  let cmd : UInt32 := cmdEndXfer ||| ((1 : UInt32) <<< 11) ||| ((rsc &&& 0x7f) <<< 16)
  let _ ← sendEpCmd base ep cmd 0 0 0

private def armEp0Setup (d : Device) : BaseIO Device := do
  let rsc ← startTrb d.base 0 d.ep0OutTrb d.setupBuf 8 trbCtrlSetup
  return { d with ep0Phase := .setup, ep0OutRsc := rsc, ep0OutActive := true }

private def configureEp0 (base : UInt64) (mps : UInt32 := 64) : BaseIO Unit := do
  let _ ← sendEpCmd base 0 cmdStartNewCfg 0 0 0
  -- EP0-OUT (phys 0): Control (0), mps, FIFO 0, XferComplete + XferNotReady, USB EP 0
  let p0Out : UInt32 := (mps &&& 0x7ff) <<< 3
  let p1Out : UInt32 := ((1 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 10) ||| ((0 : UInt32) <<< 25)
  let _ ← sendEpCmd base 0 cmdSetEpCfg p0Out p1Out 0
  let _ ← sendEpCmd base 0 cmdSetXferRes 1 0 0
  -- EP0-IN (phys 1): Control (0), mps, FIFO 0, XferComplete + XferNotReady, USB EP 1
  let p0In : UInt32 := (mps &&& 0x7ff) <<< 3
  let p1In : UInt32 := ((1 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 10) ||| ((1 : UInt32) <<< 25)
  let _ ← sendEpCmd base 1 cmdSetEpCfg p0In p1In 0
  let _ ← sendEpCmd base 1 cmdSetXferRes 1 0 0
  Hw.write32 (base + regDalepena) 0x3

private def modifyEp0Mps (base : UInt64) (mps : UInt32 := 64) : BaseIO Unit := do
  -- DEPCFG Action = 2 (Modify, bits [31:30]) updates MPS without disrupting active SETUP TRB!
  let actMod : UInt32 := (2 : UInt32) <<< 30
  let p0Out : UInt32 := actMod ||| ((mps &&& 0x7ff) <<< 3)
  let p1Out : UInt32 := ((1 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 10) ||| ((0 : UInt32) <<< 25)
  let _ ← sendEpCmd base 0 cmdSetEpCfg p0Out p1Out 0
  let p0In : UInt32 := actMod ||| ((mps &&& 0x7ff) <<< 3)
  let p1In : UInt32 := ((1 : UInt32) <<< 8) ||| ((1 : UInt32) <<< 10) ||| ((1 : UInt32) <<< 25)
  let _ ← sendEpCmd base 1 cmdSetEpCfg p0In p1In 0

private def configureBulkEps (d : Device) : BaseIO Device := do
  if d.configured && d.bulkOutArmed then
    return d
  -- Re-start resource allocation from index 2 (leaves EP0 phys 0,1 untouched!)
  let _ ← sendEpCmd d.base 0 (cmdStartNewCfg ||| ((2 : UInt32) <<< 16)) 0 0 0
  let mps : UInt32 := d.bulkMaxPkt.toUInt32
  -- Bulk-OUT (phys 2 -> USB EP1 OUT = 0x01, usbEpNum = 2): EPType=2 (Bulk), FIFO 0
  let p0Out : UInt32 := ((2 : UInt32) <<< 1) ||| ((mps &&& 0x7ff) <<< 3)
  let p1Out : UInt32 := ((1 : UInt32) <<< 8) ||| ((2 : UInt32) <<< 25)
  let _ ← sendEpCmd d.base 2 cmdSetEpCfg p0Out p1Out 0
  let _ ← sendEpCmd d.base 2 cmdSetXferRes 1 0 0
  -- Bulk-IN (phys 3 -> USB EP1 IN = 0x81, usbEpNum = 3): EPType=2 (Bulk), FIFO 1
  let p0In : UInt32 := ((2 : UInt32) <<< 1) ||| ((mps &&& 0x7ff) <<< 3) ||| ((1 : UInt32) <<< 17)
  let p1In : UInt32 := ((1 : UInt32) <<< 8) ||| ((3 : UInt32) <<< 25)
  let _ ← sendEpCmd d.base 3 cmdSetEpCfg p0In p1In 0
  let _ ← sendEpCmd d.base 3 cmdSetXferRes 1 0 0
  Hw.write32 (d.base + regDalepena) 0xF
  -- Arm Bulk-OUT TRB to receive incoming `Kernel.Wire` frames
  let _ ← startTrb d.base 2 d.bulkOutTrb d.bulkOutBuf 4096 trbCtrlNormal
  return { d with configured := true, bulkOutArmed := true, bulkOutReqLen := 4096, bulkInBusy := false }

private def delayUs (us : UInt64) : BaseIO Unit := do
  -- Tensor G4 CNTVCT_EL0 ticks at ~24.576 MHz (~25 ticks/us)
  let t0 ← Hw.ticks
  let need := us * 25
  for _ in [0:1000000] do
    let t1 ← Hw.ticks
    if t1 - t0 ≥ need then break
    Hw.pause

/-- Wakes the link block and the eUSB2 PHY, as the vendor's drivers do (`exynos-usb-blkcon.c` init_link,
`phy-exynos-eusb.c` `phy_exynos_eusb_initiate`). Done once at start, and again by `Device.reconnect` when
restarting the controller alone has not brought a host back. -/
private def wakePhy (hasBlk hasEusb : Bool) : BaseIO Unit := do
  -- 0b. Bring up Tensor G4 `usbdrd_blkcon` (`exynos-usb-blkcon.c`: init_link + detach_pipe3_phy)
  --     CRITICAL: set `dis_buspend_qact` (bit 13) so HWACG NEVER clock-gates DWC3 when macOS autosuspends USB!
  if hasBlk then
    let lc0 ← Hw.read32 (usbBlkconBase + blkconLinkCtrl)
    let lc1 : UInt32 := (lc0 &&& (~~~((1 : UInt32) <<< 8))) ||| 0x00003E00 -- dis_*_qact [13:9] incl. buspend, force_qact=0
    Hw.write32 (usbBlkconBase + blkconLinkCtrl) lc1
    delayUs 500
    -- force_qact=1 [8], bus_filter_bypass=0xf [7:4], force_pipe_en [16], force_phystatus=0 [17], force_rxelecidle [18]
    let lc2 : UInt32 := (lc1 &&& (~~~((1 : UInt32) <<< 17))) ||| 0x000501F0
    Hw.write32 (usbBlkconBase + blkconLinkCtrl) lc2
    -- Pulse link_sw_rst (bit 0) and select suspend_clk (`link_pclk_sel = 0`, bit 1)
    let cr0 ← Hw.read32 (usbBlkconBase + blkconLinkClkRst)
    Hw.write32 (usbBlkconBase + blkconLinkClkRst) ((cr0 &&& (~~~(2 : UInt32))) ||| 1)
    delayUs 20
    Hw.write32 (usbBlkconBase + blkconLinkClkRst) (cr0 &&& (~~~(3 : UInt32)))
    -- Assert force_bvalid (bit 0) | force_vbusvalid (bit 1) (`is_not_vbus_pad = 1`)
    let utmi ← Hw.read32 (usbBlkconBase + blkconUtmiCtrl)
    Hw.write32 (usbBlkconBase + blkconUtmiCtrl) (utmi ||| 0x3)

  -- 0c. Wake Tensor G4 4nm eUSB2 PHY (`phy-exynos-eusb.c` `phy_exynos_eusb_initiate`, ver 0x701, 19.2MHz)
  if hasEusb then
    -- Step 1: Assert phy_reset + utmi_port_reset with override enables
    let r0 ← Hw.read32 (usbEusbconBase + eusbconRstCtrl)
    Hw.write32 (usbEusbconBase + eusbconRstCtrl) (r0 ||| 0x33)
    -- Step 2: Configure repeater mode (`phy_cfg_rptr_mode = 1`, bit 10), 19.2MHz (`ref_freq_sel = 0`), `retenable_n = 1`
    let cm0 ← Hw.read32 (usbEusbconBase + eusbconCmnCtrl)
    let cm1 : UInt32 := (cm0 &&& (~~~(0x71 : UInt32))) ||| 0x0402 -- phy_enable=0, ref_freq_sel=0, rptr_mode=1, retenable_n=1
    Hw.write32 (usbEusbconBase + eusbconCmnCtrl) cm1
    -- PLL: 19.2MHz -> fb_div=368 (0x170 << 8), cpbias_cntrl=0 ([6:0]), ref_div=0 ([11:8])
    let p0 ← Hw.read32 (usbEusbconBase + eusbconPllCfg0)
    let p0' : UInt32 := (p0 &&& (~~~(0x000FFF7F : UInt32))) ||| ((368 : UInt32) <<< 8)
    Hw.write32 (usbEusbconBase + eusbconPllCfg0) p0'
    let p1 ← Hw.read32 (usbEusbconBase + eusbconPllCfg1)
    Hw.write32 (usbEusbconBase + eusbconPllCfg1) (p1 &&& (~~~(0x0F00 : UInt32)))
    -- Keep UTMI clock running (`clk_force_en = 1`, bit 0) + `vbus_valid_ext = 1` (bits 11, 12)
    let eu0 ← Hw.read32 (usbEusbconBase + eusbconUtmi)
    Hw.write32 (usbEusbconBase + eusbconUtmi) (eu0 ||| 0x1801)
    -- Step 3: Clear test_iddq (bit 6) to power up analog circuits
    let ts0 ← Hw.read32 (usbEusbconBase + eusbconTestSe)
    Hw.write32 (usbEusbconBase + eusbconTestSe) (ts0 &&& (~~~((1 : UInt32) <<< 6)))
    delayUs 20
    -- Step 6: Release phy_reset (bit 0 = 0)
    let r1 ← Hw.read32 (usbEusbconBase + eusbconRstCtrl)
    Hw.write32 (usbEusbconBase + eusbconRstCtrl) (r1 &&& (~~~(1 : UInt32)))
    delayUs 20
    -- Step 7: Set phy_enable = 1 (bit 0), wait 4ms for REXT cal + eUSB ESE1 port reset
    let cm2 ← Hw.read32 (usbEusbconBase + eusbconCmnCtrl)
    Hw.write32 (usbEusbconBase + eusbconCmnCtrl) (cm2 ||| 1)
    delayUs 4000
    -- Release utmi_port_reset (bit 4) & override (bit 5)
    let r2 ← Hw.read32 (usbEusbconBase + eusbconRstCtrl)
    Hw.write32 (usbEusbconBase + eusbconRstCtrl) (r2 &&& (~~~(0x30 : UInt32)))

/-- Stops the controller, resets it, and starts it again as a high-speed device waiting for a host, with
the buffers `d` already has. This is how the driver starts, and how it starts over (`Device.reconnect`). -/
private def startCore (d : Device) : BaseIO Device := do
  let base := d.base
  let evBuf := d.evBuf
  -- 1. Stop controller (wait DEVCTRLHLT bit 22), then issue device-only soft reset (`DCTL.CSFTRST`)
  let dctl0 ← Hw.read32 (base + regDctl)
  Hw.write32 (base + regDctl) (dctl0 &&& (~~~((1 : UInt32) <<< 31)))
  for _ in [0:100000] do
    let dsts ← Hw.read32 (base + regDsts)
    if (dsts &&& ((1 : UInt32) <<< 22)) != 0 then break
    Hw.pause
  Hw.write32 (base + regDctl) ((1 : UInt32) <<< 30)
  for _ in [0:400000] do
    let r ← Hw.read32 (base + regDctl)
    if (r &&& ((1 : UInt32) <<< 30)) == 0 then break
    Hw.pause

  -- 1b. Keep both USB2 & USB3 PHYs awake (`dwc3_core_susphy_set(dwc, 0)` from `dwc3-exynos.c`)
  let p3cfg ← Hw.read32 (base + regGusb3PipeCtl0)
  Hw.write32 (base + regGusb3PipeCtl0) (p3cfg &&& (~~~((1 : UInt32) <<< 17)))
  let pcfg ← Hw.read32 (base + regGusb2PhyCfg0)
  Hw.write32 (base + regGusb2PhyCfg0) (pcfg &&& (~~~(0x40000140 : UInt32)))

  -- 2. Force Device role (`GCTL.PRTCAPDIR = 2`), disable internal clock gating (`DSBLCLKGTNG = 1`)
  --    & hibernation (`GBLHIBERNATIONEN = 0`), and set High-Speed (`DCFG.DEVSPD = 0`, `NUMP = 4`)
  let gctl ← Hw.read32 (base + regGctl)
  let gctl' := (gctl &&& (~~~(((3 : UInt32) <<< 12) ||| 2))) ||| ((2 : UInt32) <<< 12) ||| 1
  Hw.write32 (base + regGctl) gctl'
  let dcfg ← Hw.read32 (base + regDcfg)
  let dcfg' : UInt32 := (dcfg &&& (~~~(0x003E03FF : UInt32))) ||| ((4 : UInt32) <<< 17) -- DEVSPD=0 (HS), DEVADDR=0, NUMP=4
  Hw.write32 (base + regDcfg) dcfg'

  -- 3. Install 4 KiB polled event ring (INTMASK=1 so IRQ stays masked)
  Hw.write32 (base + regGevntAdrLo0) evBuf.toUInt32
  Hw.write32 (base + regGevntAdrHi0) (evBuf >>> 32).toUInt32
  Hw.write32 (base + regGevntSiz0) ((4096 : UInt32) ||| ((1 : UInt32) <<< 31))
  Hw.write32 (base + regGevntCount0) 0

  -- 4. Enable Disconnect + USB Reset + Connect Done device events
  Hw.write32 (base + regDevten) 0x7

  -- 5. Configure EP0-OUT & EP0-IN and arm initial 8-byte SETUP TRB
  configureEp0 base 64
  let d0 : Device := { d with
    evPos := 0, ep0Phase := .setup, ep0OutRsc := 0, ep0InRsc := 0, ep0OutActive := false, ep0InActive := false,
    configured := false, bulkOutArmed := false, bulkInBusy := false, clkGated := false,
    rxAccum := ByteArray.empty }
  let d1 ← armEp0Setup d0

  -- 6. Connect to USB host (`DCTL.RUN_STOP = 1`, U1/U2 disabled per `dwc3-exynos.c`)
  let dctl1 ← Hw.read32 (base + regDctl)
  let dctl2 := (dctl1 &&& (~~~((1 : UInt32) <<< 10 ||| (1 : UInt32) <<< 12))) ||| ((1 : UInt32) <<< 31)
  Hw.write32 (base + regDctl) dctl2
  return d1

/-- Safe probe & initialization of Synopsys DWC3 in USB 2.0 High-Speed Device mode.
    Includes Tensor G4 (`zumapro`) `phy_exynos_eusb_initiate` + `exynos_usbcon_init_link` wakeup! -/
def init (base : UInt64 := dwc3DefaultBase) : BaseIO (Except String Device) := do
  let wins ← Hw.windows
  let hasWin (a len : UInt64) : Bool :=
    wins.any fun w => a ≥ w.base && w.size ≥ len && a - w.base ≤ w.size - len
  if !hasWin base 0xD000 then
    return .error "DWC3_NO_WINDOW"
  if hasWin pmuPdHsi0Status 4 then
    let pd ← Hw.read32 pmuPdHsi0Status
    -- On Tensor G4 (`zumapro`), PMU_ALIVE STATUS bit 0 (`0x1`) = powered ON!
    if (pd &&& 0x1) == 0 then
      return .error s!"USB_PD_HSI0_OFF({pd})"

  -- Note: `PMU_ALIVE + 0x3EB0` (`USBDP_PHY_ISO`) is an EL3-privileged register (`rmw_priv_reg` in
  -- `phy-exynos-usbdrd-eusb.c`); NEVER write it directly from EL1 (direct NS write trips Tensor G4's
  -- PMU firewall and locks out subsequent `ARM_SMCCC_TRNG_RND64` calls!). ABL already leaves it un-isolated.

  wakePhy (hasWin usbBlkconBase 0x20) (hasWin usbEusbconBase 0x30)

  let snps ← Hw.read32 (base + regGsnpsId)
  let hi := snps >>> 16
  if hi != 0x5533 && hi != 0x3331 && hi != 0x3332 then
    return .error s!"USB_BAD_SNPSID({snps})"

  -- Allocate DMA buffers (4 KiB page-aligned in Normal-NC DMA arena)
  let evBuf ← Hw.alloc 4096
  let trbPage ← Hw.alloc 4096
  let setupBuf ← Hw.alloc 4096
  let ep0DataBuf ← Hw.alloc 4096
  let bulkOutBuf ← Hw.alloc 4096
  let bulkInBuf ← Hw.alloc 4096
  if evBuf == 0 || trbPage == 0 || setupBuf == 0 || ep0DataBuf == 0 || bulkOutBuf == 0 || bulkInBuf == 0 then
    return .error "USB_DMA_ALLOC_FAIL"

  let d0 : Device := {
    base, snpsId := snps, evBuf, trbPage, setupBuf, ep0DataBuf, bulkOutBuf, bulkInBuf,
    hasPmu := hasWin pmuPdHsi0Status 4,
    hasBlkcon := hasWin usbBlkconBase 0x20,
    hasEusbcon := hasWin usbEusbconBase 0x30
  }
  return .ok (← startCore d0)

/-- Attempts to extract one complete length-prefixed `Kernel.Wire` frame from `rxAccum`. -/
private def tryExtractWireFrame (acc : ByteArray) : Option (Except String Wire.Frame × ByteArray) :=
  if acc.size < Wire.headerSize then none
  else
    -- Sync to "TRIW" magic if leading junk arrived
    let magicOk := acc.get! 0 == 0x54 && acc.get! 1 == 0x52 && acc.get! 2 == 0x49 && acc.get! 3 == 0x57
    if !magicOk then
      some (.error "USB_BAD_WIRE_MAGIC", ByteArray.empty)
    else
      let payloadLen := Wire.readU16Le acc 6
      let total := Wire.headerSize + payloadLen + Wire.trailerSize
      if payloadLen > Wire.maxPayload then
        some (.error "USB_PAYLOAD_TOO_LARGE", ByteArray.empty)
      else if acc.size < total then
        none
      else
        let frameBytes := acc.extract 0 total
        let rest := acc.extract total acc.size
        some (Wire.decode frameBytes, rest)

/-- Polls DWC3 hardware event buffer once; handles USB enumeration and yields any received `Wire.Frame`. -/
def Device.pollFrame (d : Device) : BaseIO (Device × Option (Except String Wire.Frame)) := do
  -- First check if `rxAccum` already contains a full frame
  if let some (res, rest) := tryExtractWireFrame d.rxAccum then
    return ({ d with rxAccum := rest }, some res)

  -- Hardware AXI-hang guard: NEVER touch DWC3 if PD_HSI0 is off or HWACG gated the external bus clock!
  if d.hasPmu then
    let pd ← Hw.read32 pmuPdHsi0Status
    if (pd &&& 0x1) == 0 then
      return ({ d with clkGated := true }, none)
  if d.hasBlkcon then
    let lc ← Hw.read32 (usbBlkconBase + blkconLinkCtrl)
    if (lc &&& ((1 : UInt32) <<< 24)) != 0 then
      Hw.write32 (usbBlkconBase + blkconLinkCtrl) (lc ||| 0x00003F00)
      return ({ d with clkGated := true }, none)

  let cnt := ((← Hw.read32 (d.base + regGevntCount0)) &&& 0xFFFF).toNat
  if cnt < 4 then return (d, none)

  let mut cur := d
  let mut emitted : Option (Except String Wire.Frame) := none
  let nEvents := min (cnt / 4) 32
  for _ in [0:nEvents] do
    let evBytes ← Hw.load (cur.evBuf + cur.evPos.toUInt64) 4
    let ev := readLe32 evBytes 0
    cur := { cur with evPos := (cur.evPos + 4) % cur.evSize, evSeen := cur.evSeen + 1, lastEv := ev }
    Hw.write32 (cur.base + regGevntCount0) 4

    if (ev &&& 1) != 0 then
      -- Device-specific event
      let evType := (ev >>> 8) &&& 0xF
      if evType == 1 then
        -- USB_RESET: abort any non-SETUP active EP0 transfer, clear DEVADDR, ensure SETUP is armed!
        if cur.ep0InActive then
          endXfer cur.base 1 cur.ep0InRsc
          cur := { cur with ep0InActive := false }
        if cur.ep0OutActive && cur.ep0Phase != .setup then
          endXfer cur.base 0 cur.ep0OutRsc
          cur := { cur with ep0OutActive := false }
        let dcfg ← Hw.read32 (cur.base + regDcfg)
        Hw.write32 (cur.base + regDcfg) (dcfg &&& (~~~((0x7F : UInt32) <<< 3)))
        let resetDev := { cur with configured := false, bulkOutArmed := false, rxAccum := ByteArray.empty }
        cur ← if resetDev.ep0OutActive && resetDev.ep0Phase == .setup then pure resetDev else armEp0Setup resetDev
      else if evType == 2 then
        -- CONNECT_DONE: detect negotiated speed (0=HS -> 512B bulk, else 64B bulk), modify EP0 MPS cleanly
        let dsts ← Hw.read32 (cur.base + regDsts)
        let spd := dsts &&& 0x7
        let bulkMps : UInt16 := if spd == 0 then 512 else 64
        modifyEp0Mps cur.base 64
        let connDev := { cur with bulkMaxPkt := bulkMps }
        cur ← if connDev.ep0OutActive && connDev.ep0Phase == .setup then pure connDev else armEp0Setup connDev
      else if evType == 0 then
        -- DISCONNECT
        cur := { cur with configured := false, bulkOutArmed := false, rxAccum := ByteArray.empty }
    else
      -- Endpoint-specific event
      let ep := ((ev >>> 1) &&& 0x1F).toNat
      let evType := (ev >>> 6) &&& 0xF
      let evStat := (ev >>> 12) &&& 0xF
      if ep == 0 && evType == 1 then
        -- EP0-OUT XferComplete
        cur := { cur with ep0OutActive := false }
        if cur.ep0Phase == .setup then
          let rawSetup ← Hw.load cur.setupBuf 8
          match decodeSetup rawSetup with
          | none =>
            let _ ← sendEpCmd cur.base 0 cmdSetStall 0 0 0
            cur ← armEp0Setup cur
          | some req =>
            cur := { cur with lastSetupReq := req.bRequest, lastSetupVal := req.wValue }
            match handleStandardSetup req cur.bulkMaxPkt with
            | .sendData payload =>
              Hw.store cur.ep0DataBuf payload
              let rsc ← startTrb cur.base 1 cur.ep0InTrb cur.ep0DataBuf payload.size.toUInt32 trbCtrlData
              cur := { cur with ep0Phase := .dataIn, ep0InRsc := rsc, ep0InActive := true }
            | .setAddress addr =>
              let dcfg ← Hw.read32 (cur.base + regDcfg)
              let dcfg' := (dcfg &&& (~~~((0x7F : UInt32) <<< 3))) ||| ((addr.toUInt32 &&& 0x7F) <<< 3)
              Hw.write32 (cur.base + regDcfg) dcfg'
              -- Wait for XferNotReady (Control Status) on EP0-IN before starting STATUS2 TRB!
              cur := { cur with ep0Phase := .waitStatusIn }
            | .setConfiguration _ =>
              cur ← configureBulkEps cur
              cur := { cur with ep0Phase := .waitStatusIn }
            | .ackZero =>
              cur := { cur with ep0Phase := .waitStatusIn }
            | .stall =>
              let _ ← sendEpCmd cur.base 0 cmdSetStall 0 0 0
              cur ← armEp0Setup cur
        else if cur.ep0Phase == .statusOut then
          cur ← armEp0Setup cur
      else if ep == 1 && evType == 1 then
        -- EP0-IN XferComplete
        cur := { cur with ep0InActive := false }
        if cur.ep0Phase == .dataIn then
          -- Wait for XferNotReady (Control Status) on EP0-OUT before starting STATUS3 TRB!
          cur := { cur with ep0Phase := .waitStatusOut }
        else if cur.ep0Phase == .statusIn then
          cur ← armEp0Setup cur
      else if evType == 3 then
        -- EP0 XferNotReady: Synopsys DWC3 Databook §8.4 (bits [13:12] == 2 -> Control Status stage ready!)
        let stage := evStat &&& 0x3
        if ep == 0 && cur.ep0Phase == .waitStatusOut && stage == 2 then
          let rsc ← startTrb cur.base 0 cur.ep0OutTrb cur.setupBuf 0 trbCtrlStatus3
          cur := { cur with ep0Phase := .statusOut, ep0OutRsc := rsc, ep0OutActive := true }
        else if ep == 1 && cur.ep0Phase == .waitStatusIn && stage == 2 then
          let rsc ← startTrb cur.base 1 cur.ep0InTrb cur.ep0DataBuf 0 trbCtrlStatus2
          cur := { cur with ep0Phase := .statusIn, ep0InRsc := rsc, ep0InActive := true }
      else if ep == 2 && evType == 1 then
        -- Bulk-OUT EP1 (`0x01`) XferComplete: compute actual received bytes = reqLen - trb.bufsiz
        let trbBytes ← Hw.load cur.bulkOutTrb 16
        let remain := (readLe32 trbBytes 8 &&& 0x00FFFFFF).toNat
        let got := if cur.bulkOutReqLen ≥ remain then cur.bulkOutReqLen - remain else 0
        if got > 0 then
          let chunk ← Hw.load cur.bulkOutBuf got.toUSize
          cur := { cur with rxAccum := cur.rxAccum ++ chunk }
        -- Immediately re-arm Bulk-OUT for next packet!
        let _ ← startTrb cur.base 2 cur.bulkOutTrb cur.bulkOutBuf 4096 trbCtrlNormal
        cur := { cur with bulkOutArmed := true, bulkOutReqLen := 4096 }
        if emitted.isNone then
          if let some (res, rest) := tryExtractWireFrame cur.rxAccum then
            cur := { cur with rxAccum := rest }
            emitted := some res
      else if ep == 3 && evType == 1 then
        -- Bulk-IN EP1 (`0x81`) XferComplete
        cur := { cur with bulkInBusy := false }

  return (cur, emitted)

/-- One look at the link, for `Kernel.UsbLink`: the controller's status and control registers, read only,
and only when its power domain is on and its bus clock is not gated, as `pollFrame` insists. The status
keeps its speed (bits 2:0), link state (21:18) and halted bit (22); the frame counter is masked off. -/
def Device.sample (d : Device) (ticks : Nat) : BaseIO UsbLink.Sample := do
  let gatedNow : UsbLink.Sample :=
    { ticks, events := d.evSeen, lastEv := d.lastEv, configured := d.configured, gated := true }
  if d.hasPmu then
    if ((← Hw.read32 pmuPdHsi0Status) &&& 0x1) == 0 then return gatedNow
  if d.hasBlkcon then
    if ((← Hw.read32 (usbBlkconBase + blkconLinkCtrl)) &&& ((1 : UInt32) <<< 24)) != 0 then return gatedNow
  let dsts ← Hw.read32 (d.base + regDsts)
  let dctl ← Hw.read32 (d.base + regDctl)
  return { ticks, dsts := dsts &&& 0x007C0007, dctl, events := d.evSeen, lastEv := d.lastEv,
           configured := d.configured, gated := d.clkGated }

/-- Starts the link over, for a host that has gone quiet (`Kernel.UsbLink.Watch`): the controller is stopped,
which takes the signer off the bus, and started again, which puts it back for the host to find. With
`phy`, the link block and the eUSB2 PHY are woken again first, as at start. Nothing is done if the
controller's power domain is off or its clock is gated. The count of events seen is kept. -/
def Device.reconnect (d : Device) (phy : Bool) : BaseIO Device := do
  if d.hasPmu then
    if ((← Hw.read32 pmuPdHsi0Status) &&& 0x1) == 0 then return d
  if d.hasBlkcon then
    if ((← Hw.read32 (usbBlkconBase + blkconLinkCtrl)) &&& ((1 : UInt32) <<< 24)) != 0 then return d
  if phy then wakePhy d.hasBlkcon d.hasEusbcon
  startCore d

/-- Transmits one CRC-32-protected `Kernel.Wire.Frame` over USB-C Bulk-IN (`0x81`). -/
def Device.sendFrame (d : Device) (f : Wire.Frame) : BaseIO Device := do
  if !d.configured then return d
  let bytes := Wire.encode f
  if bytes.size == 0 || bytes.size > 4096 then return d
  Hw.store d.bulkInBuf bytes
  let _ ← startTrb d.base 3 d.bulkInTrb d.bulkInBuf bytes.size.toUInt32 trbCtrlNormal
  -- Wait briefly for Bulk-IN completion so consecutive replies stay strictly ordered
  let mut cur := { d with bulkInBusy := true }
  for _ in [0:400000] do
    let trbBytes ← Hw.load cur.bulkInTrb 16
    let ctrl := readLe32 trbBytes 12
    if (ctrl &&& trbHwo) == 0 then
      return { cur with bulkInBusy := false }
    Hw.pause
  return cur

end Kernel.Dwc3
