import Kernel.Hw
import Kernel.Fdt

/-! # Pixel 9 Pro XL (`komodo` / Tensor G4 `zumapro`) Hardware Discovery & Register Map

Discovers all Tensor G4 (`zumapro`) peripherals dynamically from the live Flattened Device Tree
passed by Pixel ABL in `x0` (zero hardcoded blind pokes: every MMIO access is still bounded by
`Hw.windows`!).

Target subsystems for Phase 2 live bring-up on slot `_b`:
- **Display**: ABL `cont_splash` framebuffer (`simple-framebuffer` / `reserved-memory`) +
  Exynos DECON command-mode flush (`samsung,exynos-decon`)
- **Physical Buttons**: Exynos `GPA*` GPIO bank (`samsung,exynos-pinctrl` / `gpio-keys`)
- **Watchdog**: Samsung `s3c2410-wdt` (`samsung,exynos-wdt` / `samsung,s3c2410-wdt`)
- **Raw 2-Slot Vault Storage**: Polled Exynos UFSHCI 3.1/4.0 (`samsung,exynos-ufs`)
- **USB-C Wire Transport**: Polled Synopsys DWC3 (`snps,dwc3`)
- **Debug Console**: Exynos UART (`samsung,exynos-uart` / `google,exynos-usi-uart`) -/

namespace Kernel.Komodo

open Kernel.Fdt

/-- Discovered Tensor G4 (`komodo`) peripheral register bases from ABL's live FDT. -/
structure KomodoHw where
  uartBase? : Option UInt64 := none
  deconBase? : Option UInt64 := none
  wdtBase? : Option UInt64 := none
  gpioAliveBase? : Option UInt64 := none
  ufsBase? : Option UInt64 := none
  dwc3Base? : Option UInt64 := none
  splashFbBase? : Option (UInt64 × UInt64) := none
  deriving Repr, Inhabited

private def firstReg (nodes : Array FdtNode) : Option (UInt64 × UInt64) :=
  match nodes[0]? with
  | some n => n.regs[0]?
  | none => none

/-- Populates `KomodoHw` purely from the verified FDT parsed from ABL's `x0`. -/
def discoverFromFdt (fdt : ParsedFdt) : KomodoHw :=
  let findAny (compats : List String) : Option (UInt64 × UInt64) :=
    compats.findSome? fun c => firstReg (fdt.findCompatible c)
  let splash := findAny ["simple-framebuffer"]
    <|> (fdt.nodes.find? (fun n => n.name.startsWith "cont_splash" || n.name.startsWith "splash")
          |>.bind (·.regs[0]?))
  {
    uartBase? := (findAny ["google,exynos-usi-uart", "samsung,exynos4210-uart", "samsung,exynos-uart"]).map (·.1)
    deconBase? := (findAny ["samsung,exynos9-decon", "samsung,exynos-decon", "google,zumapro-decon"]).map (·.1)
    wdtBase? := (findAny ["samsung,s3c2410-wdt", "samsung,exynos850-wdt", "samsung,exynos-wdt"]).map (·.1)
    gpioAliveBase? := (findAny ["google,zumapro-pinctrl", "samsung,zumapro-pinctrl", "samsung,exynos-pinctrl"]).map (·.1)
    ufsBase? := (findAny ["samsung,exynos-ufs", "jedec,ufs-2.0"]).map (·.1)
    dwc3Base? := (findAny ["snps,dwc3"]).map (·.1)
    splashFbBase? := splash
  }

/-! ## Samsung `s3c2410-wdt` Watchdog Disarm/Pet (`WTCON = +0x00`) -/

def wdtRegCon : UInt64 := 0x00
def wdtRegDat : UInt64 := 0x04
def wdtRegCnt : UInt64 := 0x08
def wdtRegClrInt : UInt64 := 0x0C

def wdtCl0DefaultBase : UInt64 := 0x10060000
def wdtCl1DefaultBase : UInt64 := 0x10070000

/-- Disables Tensor G4 `s3c2410-wdt` (`WTCON` ENABLE|INTEN|RSTEN = `0x25` + `WTCLRINT = 1`),
    matching `s3c2410_wdt.c` `s3c2410wdt_stop_intclear` verbatim. -/
def disarmWatchdog (wdtBase : UInt64) : BaseIO Unit := do
  let con ← Hw.read32 (wdtBase + wdtRegCon)
  Hw.write32 (wdtBase + wdtRegCon) (con &&& (~~~0x25))
  Hw.write32 (wdtBase + wdtRegClrInt) 1

/-! ## Official Tensor G4 (`zumapro` / `cal_9865`) DECON0 Command-Mode Flush

Verified verbatim from `kernel/google-modules/display/samsung/cal_9865/{regs-decon.h,decon_reg.c}`:
- `DECON0_MAIN` = `0x19470000`
- `GLOBAL_CON` = `+0x0020` (`DECON_EN = 1<<1`, `DECON_EN_F = 1<<0`)
- `TRIG_CON`   = `+0x0030` (`SW_TRIG_EN = 1<<8`, `HW_TRIG_MASK_DECON = 1<<4`, `SW_TRIG_DET_EN = 1<<1`, `HW_TRIG_EN = 1<<0`)
- `SHD_REG_UP_REQ` = `+0x0050` (`GLOBAL = 1<<31`, `CMP = 1<<20`, `WIN0..5 = 0x3f`) -/

def deconDefaultBase : UInt64 := 0x19470000
def deconRegGlobalCon : UInt64 := 0x0020
def deconRegTrigCon : UInt64 := 0x0030
def deconRegShdUpReq : UInt64 := 0x0050

/-- Triggers one Tensor G4 `cal_9865` DECON0 command-mode OLED frame update after blitting to `cont_splash`. -/
def deconFlushFrame (deconBase : UInt64) : BaseIO Unit := do
  let gcon ← Hw.read32 (deconBase + deconRegGlobalCon)
  Hw.write32 (deconBase + deconRegGlobalCon) (gcon ||| 0x3)
  Hw.write32 (deconBase + deconRegShdUpReq) 0x80103FFF
  let trig ← Hw.read32 (deconBase + deconRegTrigCon)
  Hw.write32 (deconBase + deconRegTrigCon) ((trig &&& (~~~0x10)) ||| 1)

/-! ## Exynos `GPIO_ALIVE` (`pinctrl_0 = 0x154D0000`) Physical Key Polling (Active-Low)

Verified verbatim from AOSP `zuma/dts/zuma-common.dtsi` + `soc/gs/drivers/pinctrl/gs/pinctrl-gs.c`:
- `GPIO_ALIVE` (`pinctrl_0`): `0x154D0000` (always-on domain)
- `KEY_VOLUMEUP`   = `gpa6-2` (`gpa6` base `0xA0`, `DAT` = `0xA4`, bit `2`)
- `KEY_VOLUMEDOWN` = `gpa4-1` (`gpa4` base `0x80`, `DAT` = `0x84`, bit `1`)
- `KEY_POWER`      = `gpa4-0` (`gpa4` base `0x80`, `DAT` = `0x84`, bit `0`) -/

def gpioAliveDefaultBase : UInt64 := 0x154D0000

structure GpioPinConfig where
  volUpDatOffset : UInt64 := 0x00A4
  volUpBit : UInt32 := 2
  volDownDatOffset : UInt64 := 0x0084
  volDownBit : UInt32 := 1
  powerDatOffset : UInt64 := 0x0084
  powerBit : UInt32 := 0
  activeLow : Bool := true
  deriving Repr, Inhabited

def sampleGpioKeys (gpioBase : UInt64) (cfg : GpioPinConfig := {}) : BaseIO (Bool × Bool × Bool) := do
  let readPin (off : UInt64) (bit : UInt32) : BaseIO Bool := do
    let v ← Hw.read32 (gpioBase + off)
    let high := ((v >>> bit) &&& 1) != 0
    return if cfg.activeLow then !high else high
  let u ← readPin cfg.volUpDatOffset cfg.volUpBit
  let d ← readPin cfg.volDownDatOffset cfg.volDownBit
  let p ← readPin cfg.powerDatOffset cfg.powerBit
  return (u, d, p)

/-! ## Polled UFSHCI 3.1/4.0 Single-Slot Raw Block Engine (JEDEC JESD223E Standard)

Standard UFSHCI MMIO registers used by Exynos/Tensor UFS (`0x00..0x9C`):
- `HCS` (`0x30`): Host Controller Status (`DP` bit 0, `UTRLRDY` bit 1)
- `HCE` (`0x34`): Host Controller Enable (`HCE` bit 0)
- `UTRLBA` (`0x50`) / `UTRLBAU` (`0x54`): UTP Transfer Request List Base Address (1 KiB aligned)
- `UTRLDBR` (`0x58`): Transfer Request Doorbell Register
- `UTRLRSR` (`0x60`): Transfer Request Run-Stop Register -/

def ufsRegHcs : UInt64 := 0x30
def ufsRegHce : UInt64 := 0x34
def ufsRegUtrlba : UInt64 := 0x50
def ufsRegUtrlbau : UInt64 := 0x54
def ufsRegUtrldbr : UInt64 := 0x58
def ufsRegUtrlrsr : UInt64 := 0x60

structure UfsController where
  base : UInt64
  utrdBase : UInt64   -- 32-byte UTRD in DMA arena (1 KiB aligned)
  ucdBase : UInt64    -- 256-byte UCD (Command UPIU + Response UPIU + 1 PRDT entry)
  dataBase : UInt64   -- 4096-byte raw block bounce buffer
  vaultLbaBase : UInt32 -- starting 4 KiB LBA of Tricorder's dedicated raw 2-slot region
  deriving Repr, Inhabited

/-- Initializes UFSHCI slot 0 transfer list when controller is already link-up from ABL. -/
def UfsController.attach (ufsBase : UInt64) (vaultLbaBase : UInt32) : BaseIO (Option UfsController) := do
  let hce ← Hw.read32 (ufsBase + ufsRegHce)
  if (hce &&& 1) == 0 then return none
  let hcs ← Hw.read32 (ufsBase + ufsRegHcs)
  if (hcs &&& 0x03) != 0x03 then return none -- Device Present & UTRL Ready required
  let utrdBase ← Hw.alloc 4096
  let ucdBase ← Hw.alloc 4096
  let dataBase ← Hw.alloc 4096
  if utrdBase == 0 || ucdBase == 0 || dataBase == 0 then return none
  Hw.write32 (ufsBase + ufsRegUtrlba) utrdBase.toUInt32
  Hw.write32 (ufsBase + ufsRegUtrlbau) (utrdBase >>> 32).toUInt32
  Hw.write32 (ufsBase + ufsRegUtrlrsr) 1
  return some { base := ufsBase, utrdBase, ucdBase, dataBase, vaultLbaBase }

/-! ## Polled Synopsys DWC3 USB-C Bulk Device Core (`snps,dwc3`)

Standard Synopsys DWC3 global & device register offsets (`0xC100..0xC800`):
- `GSNPSID` (`0xC120`): Synopsys Core ID (`0x5533xxxx` = USB3, `0x3331xxxx` = USB3.1)
- `DCFG` (`0xC700`), `DCTL` (`0xC704`), `DSTS` (`0xC70C`)
- `GEVNTADRLO(0)` (`0xC400`), `GEVNTSIZ(0)` (`0xC408`), `GEVNTCOUNT(0)` (`0xC40C`) -/

def dwc3RegSnpsId : UInt64 := 0xC120
def dwc3RegDcfg : UInt64 := 0xC700
def dwc3RegDctl : UInt64 := 0xC704
def dwc3RegDsts : UInt64 := 0xC70C

/-- Probes a `snps,dwc3` MMIO window and returns its Synopsys Core ID if present. -/
def probeDwc3 (dwc3Base : UInt64) : BaseIO UInt32 :=
  Hw.read32 (dwc3Base + dwc3RegSnpsId)

end Kernel.Komodo
