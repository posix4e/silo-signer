# Silo Signer (`silo-signer`)

A **100% bare-metal, formally verified AArch64 Lean 4 hardware signer** — zero Linux, zero Android, zero libc, zero filesystems, zero third-party SDK/NDK — turning a **Google Pixel 9 Pro XL (`komodo` / Tensor G4)** (and QEMU `-M virt`) into the dedicated offline human-in-the-loop companion to **[`silo`](https://github.com/posix4e/silo)** and **[`silo-os`](https://github.com/posix4e/silo-os)**.

## Role in the Silo Architecture

[`silo`](https://github.com/posix4e/silo) runs an exchange/treasury hot-wallet co-signer inside an AWS Nitro Enclave on [`silo-os`](https://github.com/posix4e/silo-os) (a Lean 4 unikernel). **`silo-signer`** brings that exact same formally verified Lean 4 minimal runtime (`Runtime/`, `Mini/`, `rt/`, `Kernel/Hw.lean`) to bare-metal AArch64 handheld silicon, covering **both** human custody roles in one air-gappable device:

1. **Risk-Management Approver Wallet (`m/86'/coin'/1'/0/0`)**
   - Reviews high-value or out-of-policy withdrawal PSBTs directly on the device's OLED display (inspecting every output address, amount, and txid).
   - Signs `SHA256_tagged("silo/approve", txid)` using formally verified constant-time **BIP 340 Schnorr** (`approval <128-hex>`), exported as an ISO 18004 QR code or over CRC-32-framed USB-C.
2. **Break-Glass Recovery / Override Wallet (`m/86'/coin'/0'`)**
   - Holds the offline multisig override key for **Taproot 2-of-3** (`tr(NUMS, sortedmulti_a(k, ...))`, BIP 340) and **SegWit v0** (`wsh(sortedmulti(k, ...))`, ECDSA with mandatory full `nonWitnessUTXO` prevtx validation).
   - Allows treasury recovery even if the Nitro Enclave or hot-path infrastructure is unavailable — with zero Bitcoin node, mempool, or network stack on the device.

> **Current operational model (stateless / RAM-only on Pixel silicon):** By default on Pixel 9 Pro XL, keys live strictly in RAM (zero secrets ever written to flash; every freed Lean object is zeroed by `Mini/Alloc`). Raw 2-slot UFS persistence (`0x13200000`, zero filesystem) is tracked as an optional roadmap issue alongside touchscreen and power management.

## Verified Live on Pixel 9 Pro XL (`komodo` / Tensor G4) Silicon

Everything below has been verified end-to-end on real Pixel 9 Pro XL hardware (slot `_b`, keeping slot `_a` untouched) and in QEMU AArch64:

- **Zero OS Beneath Lean (~2.7 MB Flat ARM64 `Image`)**:
  - Boots directly from Pixel ABL (`boot_img_hdr_v4`, zero ramdisk, signed with RSA-4096 AVB2 `vbmeta.img`) into ~120 lines of EL1 assembly (`boot/aarch64/entry.S`), linked at `0xA0000000`.
  - Hardware protections active on live Cortex-X4 (`MIDR=0x410FD801`): **ARMv8.4 `PSTATE.DIT = 1`**, **Stage-1 MMU with strict `W^X` + `SCTLR_EL1.WXN = 1` + 64 KiB unmapped stack guard hole** onto a dedicated `SP_EL1` exception stack, and `-ffixed-x18` across EL3 SMCs.
  - Real hardware entropy via **EL3 `ARM_SMCCC_TRNG_RND64` (`0xC4000053`)** (with Exynos `exyswd-rng` fallback) passed through fail-closed NIST-style health checks (`Kernel/Rng.lean`).
- **Pure-Lean Bare-Metal Pixel Drivers**:
  - **OLED Display**: Live `1344×2992` `BGRA8888` handover via `DECON0_WINCON` (`0x194A0000`) / `DPUF0` `DPU_DMA` (`0x19900000`) + `DECON0_MAIN` (`0x19470000`) command-mode flush (`~10 ms` redraws) and pure-Lean ISO 18004 QR rendering.
  - **Physical Hardware Buttons**: Debounced `GPIO_ALIVE` (`0x154D0000`: Vol+ `gpa6-2`, Vol− `gpa4-1`, Power `gpa4-0`), dual Tensor G4 watchdog disarm (`0x10060000`/`0x10070000`), instant `<1 ms` `Power+VolDown` hardware reset, and `Power+VolUp` / 3 s `Power` RAM-wipe shutdown.
  - **480 Mbps USB-C Device Driver (`Kernel/Dwc3.lean`)**: Pure-Lean polled Synopsys DWC3 (`0x11210000`) + Tensor G4 4nm eUSB2 PHY (`0x11110000`) + `usbdrd_blkcon` (`0x11100000`) with HWACG bus-clock guard, carrying CRC-32 `Kernel.Wire` frames to our zero-dependency macOS IOKit CLI (`tools/tricorder_usb.c`).
- **Live Real-Silicon Bitcoin Core Signet Co-Signing Proven**:
  - Generated 24 BIP-39 words from Tensor G4 EL3 hardware TRNG, derived Signet Taproot 2-of-3 address matching **Bitcoin Core v32.1.0** byte-for-byte, signed a `1,784`-byte Taproot 2-of-3 PSBT via two-step physical-button **ARM → SIGN**, finalized & mined into a real Signet block, **and verified the `1,956`-byte signed PSBT QR code photographed off the Pixel OLED matches byte-for-byte via Apple Vision**.

## Formal Verification ([`Tricorder/Gate.lean`](Tricorder/Gate.lean))

Every theorem gated at build time compiles inside Lean's kernel with **zero `sorry`**, **zero `native_decide`/`bv_decide`**, and standard axioms `[propext, Quot.sound, Classical.choice]` only:

- **705 `SecpCt` theorems** (via pinned [`winnow-lean` `v0.9.27`](https://github.com/winnowwallet/winnow-lean)): constant-time `secp256k1` field/scalar/point ops, BIP 340 Schnorr & ECDSA sign/verify soundness.
- **`Mini.Alloc` & `Runtime.Big`**: zero-on-free heap soundness & arbitrary-precision arithmetic.
- **`Kernel.MmuProofs`**: `W^X` on every Stage-1 descriptor, `UXN=1` everywhere, Device-nGnRnE non-exec, unmapped null & stack guard pages.
- **`Kernel.FdtProofs` & `Kernel.RngProofs`**: fail-closed FDT (`0xd00dfeed`) parser and hardware RNG health checks rejecting all-zero, all-`0xFF`, and repeating words.
- **`Kernel.VaultStoreProofs`**: zero-filesystem 2-slot raw block persistence (`2 × 4 KiB` slots) with proved torn-write crash consistency, monotonic `seq` recovery, and complete two-slot zero-wipe.
- **`Kernel.WireProofs` & `Kernel.Dwc3Proofs`**: CRC-32 framing codec with proved locked-state gating, unconditional mainnet ban on host key injection, USB 2.0 descriptor bounds, and strict `wLength` clamping.
- **`Kernel.FbProofs` & `Kernel.GpioKeysProofs`**: framebuffer pixel-bounds safety, multi-tick physical-button debounce, and zero auto-repeat.
- **`Tricorder.Proofs.{StateProofs,LayoutProofs}`**: locked/pause secret wiping, 10-wrong-PIN wipe, two-step armed signing requirement, hit-test & physical-button focus soundness.

## Repository Layout

```text
boot/aarch64/     Minimal AArch64 EL1 boot stub, exception vectors, Stage-1 MMU setup, EL3 TRNG, fault checks
rt/               Verified minimal runtime + rt/bare/ (no-libc, capability-checked hw.c, platform.c)
Runtime/          Proved Lean big-number (Big) and UTF-8 (Utf8) modules
Mini/             Verified Mini-language zero-on-free allocator, arrays, strings, constant-time secret ops
Kernel/           Verified bare-metal kernel: Hw, Mmu, Fdt, Rng, VaultStore, Wire, Fb, GpioKeys,
                  Dwc3 (Synopsys USB-C + eUSB2 PHY), Qemu/{Pl011,Ramfb,VirtioMmio}, Komodo (Tensor G4)
Tricorder/        Crypto (BIP39, AES-256-GCM vault, BIP32/86), Signer (Taproot/SegWit/Approver),
                  Qr (ISO 18004), Ui (LCARS prototype + focus cursor), Proofs, Gate, ProbeMain, OsMain
MkBoot/           Pure-Lean ELF->Image flattener, boot_img_hdr_v4 packager, AVB2 RSA-4096 signer/verifier
tools/            Zero-dependency macOS native IOKit USB-C host CLI (`tricorder_usb.c`)
Tests/            SignerTest, JourneyTest, RegtestCli, BootImgTest
scripts/          build-bare, qemu-checks, qemu-regtest-e2e, build-min, build-checked, fuzz-alloc, regtest-e2e
```

## Quick Start (Fresh Clone)

Dependencies are pinned directly in `lakefile.lean` (`winnow-lean` `v0.9.27`) — no sibling repos required.

### 1. Formal Proofs & QEMU Bare-Metal Verification

```bash
# 1. Formal proof gate (705 SecpCt + Mini + Runtime + 42 Kernel/UI proofs, zero sorry)
lake build TricorderGate

# 2. Build bare-metal AArch64 QEMU probe & full OS images (requires Lean AArch64 cross libs in ~/.elan/cross/)
scripts/build-bare probe qemu regtest
scripts/build-bare os qemu regtest

# 3. Run all 9 hardware MMU fault checks in QEMU aarch64 (W^X, RO, null, stack overflow on SP_EL1, beside-device)
scripts/qemu-checks

# 4. Run full bare-metal QEMU + cold-reboot raw-block persistence + live Bitcoin Core regtest co-signing + QR scan
scripts/qemu-regtest-e2e

# 5. Hosted minimal-runtime differential, allocator fuzzing, and AVB2 tamper suite
.lake/build/bin/mini-test
scripts/fuzz-alloc 50 200
.lake/build/bin/boot-img-test
```

### 2. Pixel 9 Pro XL (`komodo`) Build, Flash & USB-C CLI

```bash
# Build signed komodo images (LOAD_BASE=0xA0000000, pure-Lean boot_img_hdr_v4 + RSA-4096 AVB2 vbmeta)
scripts/build-bare os komodo signet

# Flash to slot _b (preserves slot _a OS untouched; bootloader unlocked)
fastboot flash boot_b build/bare-os-komodo-signet/boot.img
fastboot flash --disable-verity --disable-verification vbmeta_b build/bare-os-komodo-signet/vbmeta.img
fastboot set_active b
fastboot reboot

# Compile native macOS IOKit USB-C host CLI (zero external dependencies)
clang -O2 -Wall -Wextra -framework IOKit -framework CoreFoundation \
  -o build/tricorder-usb tools/tricorder_usb.c

# Talk to the bare-metal Pixel over 480 Mbps USB-C (VID 0x1209 / PID 0x4701)
./build/tricorder-usb ping
./build/tricorder-usb status
./build/tricorder-usb keys                       # denied while locked (proved)
./build/tricorder-usb push-descriptor desc.txt   # verify & register Taproot/SegWit descriptor on OLED
./build/tricorder-usb push-override spend.psbt   # review, ARM -> SIGN with physical buttons
./build/tricorder-usb push-approve spend.psbt    # Silo Approver (`silo/approve`) BIP 340 approval
./build/tricorder-usb poll                       # retrieve signed PSBT / approval (or scan OLED QR!)
```

> Note: `build/tricorder-usb key <prev|next|select|back>` is strictly a non-mainnet test helper; `Kernel.WireProofs.mainnet_blocks_key_injection` formally proves `OP_INJECT_KEY` is unconditionally rejected on `mainnet` builds.

See [`THREAT_MODEL.md`](THREAT_MODEL.md) for the exact formal verification boundary and trusted computing base (TCB).
