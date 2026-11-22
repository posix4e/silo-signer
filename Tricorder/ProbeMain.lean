import SelfTest
import Winnow.Crypto.Sha2
import Kernel.Hw
import Kernel.Fdt
import Kernel.Rng
import Kernel.Qemu.VirtioMmio
import Kernel.Qemu.Ramfb
import Kernel.Komodo

/-! # Bare-Metal AArch64 Hardware & MMU Probe (`Tricorder.ProbeMain`)

Modeled directly on `silo-os/ProbeMain.lean`. Boots bare-metal on QEMU `-M virt -cpu max` and
Pixel 9 Pro XL (`komodo` slot `_b`), reporting:
- CPU identity (`MIDR_EL1`), initial EL, `FEAT_DIT` status, `FEAT_RNG` (`RNDR`) status
- Verified `Kernel.Fdt.parse` dump of memory ranges, `bootargs`, VirtIO & `komodo` nodes
- Hardware RNG health-checked 32-byte sample (`Kernel.Rng.collectRndr` / `VirtioRng`)
- `SelfTest.transcript` SHA-256 digest & arbitrary-precision arithmetic check on bare metal
- Runtime MMU protection checks (`check=none|write-code|write-constant|run-data|run-heap|run-stack|read-zero|overflow|beside-device`) -/

namespace Tricorder.ProbeMain

open Kernel Kernel.Qemu

private def log (s : String) : BaseIO Unit :=
  Hw.consoleWrite (s ++ "\n").toUTF8

private def hexByte (b : UInt8) : String :=
  let digits := "0123456789abcdef".toList.toArray
  let hi := digits[(b.toNat >>> 4) &&& 0xf]!
  let lo := digits[b.toNat &&& 0xf]!
  String.ofList [hi, lo]

private def hexBytes (bs : ByteArray) : String := Id.run do
  let mut s := ""
  for i in [0:bs.size] do
    s := s ++ hexByte (bs.get! i)
  return s

private def hex64 (v : UInt64) : String := Id.run do
  let digits := "0123456789abcdef".toList.toArray
  let mut cs : List Char := []
  for i in [0:16] do
    let nib := ((v >>> (UInt64.ofNat (60 - 4 * i))) &&& 0xf).toNat
    cs := cs ++ [digits[nib]!]
  return "0x" ++ String.ofList cs

@[export tricorder_bare_main]
def bareMain : IO UInt32 := do
  log "probe: Tricorder bare-metal AArch64 OS probe starting"
  let cpu ← Hw.cpuInfo
  log s!"probe: CPU MIDR={hex64 cpu.midr} initEL={cpu.currentEl} DIT={cpu.ditEnabled} RNDR={cpu.hasRndr}"
  let cmd := String.fromUTF8! (← Hw.commandLine)
  log s!"probe: bootargs: {cmd}"

  -- 1. Parse live FDT using our formally verified pure-Lean FDT parser
  let fdtRaw ← Hw.fdtBytes
  match Fdt.parse fdtRaw with
  | .error e => log s!"probe: FDT parse error ({fdtRaw.size}B): {e}"
  | .ok fdt =>
    log s!"probe: FDT OK: {fdt.memoryRanges.size} memory range(s), {fdt.nodes.size} device node(s)"
    for (b, s) in fdt.memoryRanges do
      log s!"probe:   RAM {hex64 b} size {hex64 s}"
    let kom := Komodo.discoverFromFdt fdt
    if kom.deconBase?.isSome || kom.ufsBase?.isSome || kom.dwc3Base?.isSome then
      log s!"probe:   komodo FDT: uart={kom.uartBase?.map hex64} decon={kom.deconBase?.map hex64} wdt={kom.wdtBase?.map hex64} gpio={kom.gpioAliveBase?.map hex64} ufs={kom.ufsBase?.map hex64} dwc3={kom.dwc3Base?.map hex64}"

  -- 2. Discover announced MMIO windows & VirtIO devices
  let wins ← Hw.windows
  log s!"probe: {wins.size} capability-checked MMIO windows announced"
  let vdevs ← VirtioMmio.discover
  for d in vdevs do
    log s!"probe:   virtio-mmio v2 device id={d.id} at {hex64 d.base}"

  -- 3. Hardware entropy health check (`RNDR` or `virtio-rng`)
  if cpu.hasRndr then
    match ← Rng.collectRndr 32 with
    | .ok ent => log s!"probe: RNDR health-checked 32B: {hexBytes ent}"
    | .error e => log s!"probe: RNDR FAILED: {e}"
  else
    log "probe: RNDR absent on this CPU"

  if let some vrng ← VirtioMmio.VirtioRng.init vdevs then
    if let some (_, ent) ← vrng.readBytes 32 then
      log s!"probe: virtio-rng 32B: {hexBytes ent}"

  -- 4. Pure-Lean crypto & minimal-runtime arithmetic self-test on bare metal
  let selfDig := Winnow.sha256 SelfTest.transcript
  log s!"probe: SelfTest SHA-256: {hexBytes selfDig}"
  let a : Nat := (1 <<< 256) + 0x170147
  let b : Nat := (1 <<< 129) + 1701
  let bigOk := ((a * b + 47) / b == a) && ((a * b + 47) % b == 47)
  log s!"probe: BigNat bare-metal check: {bigOk}"

  -- 5. Run MMU fault-injection check if `check=<name>` was requested on bootargs!
  let chk ← Hw.bootCheck
  if chk == 0 then
    log "probe: boot check passed (exit 0)"
    return 0
  else if chk == 1 then
    log "probe: no check= requested; probe complete"
    return 0
  else
    log s!"probe: boot check returned unexpected code {chk}"
    return chk

/-- Dummy hosted main so Lake computes the full C transitive closure cleanly. -/
def main : IO UInt32 := bareMain

end Tricorder.ProbeMain
