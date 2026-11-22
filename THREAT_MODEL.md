# Silo Signer Threat Model & Verification Boundary

This document strictly separates what **Silo Signer** (`silo-signer`) **formally proves inside Lean's trusted kernel**, what it **verifies mechanically on bare-metal AArch64 (QEMU + Pixel 9 Pro XL silicon) & Bitcoin Core**, and what remains in the **trusted computing base (TCB)**.

## 1. Formally Proved (`Tricorder/Gate.lean`)

Every theorem checked in `Tricorder/Gate.lean` compiles with **zero `sorry`**, **zero `native_decide`/`bv_decide`**, and depends **only** on Lean's standard three axioms (`propext`, `Quot.sound`, `Classical.choice`):

- **Cryptography (`SecpCt.Gate` — 705 theorems, pinned via `winnow-lean` `v0.9.27`)**:
  - Constant-time `secp256k1` field, scalar, and Jacobian point arithmetic.
  - BIP 340 Schnorr signing & verification soundness (`sign_eq`, `verify_sound`, `verify_sign`, `signVerified_verifies`) — covering Taproot multisig spends and `SHA256_tagged("silo/approve", txid)` risk-management approvals.
  - ECDSA signing & verification soundness (`Ecdsa.sign_eq`, `Ecdsa.verify_sound`, `Ecdsa.signVerified_verifies`) — covering SegWit v0 `wsh(sortedmulti)` recovery spends.
- **Verified Minimal Runtime (`Proofs.lean`, `Mini/*Proofs.lean`, `Runtime/*Proofs.lean`, shared with `silo-os`)**:
  - `Mini.Alloc`: disjointness, heap safety, and **zero-on-free** (every freed object is overwritten with zeros).
  - `Mini.Secret`: constant-time byte compare & word select (taint-checked in `mini-test`).
  - `Runtime.Big` & `Runtime.Utf8`: arbitrary-precision arithmetic and strict UTF-8 decoding.
- **Bare-Metal AArch64 Kernel (`Kernel/*Proofs.lean`)**:
  - `Kernel.MmuProofs`: Stage-1 VMSAv8-64 `W^X` on every encoded descriptor, `UXN=1` everywhere, `Device-nGnRnE` strictly non-executable, unmapped null page (`0x0`) and stack guard page (`__stack_guard`).
  - `Kernel.FdtProofs`: fail-closed Flattened Device Tree (`0xd00dfeed`) header/bounds validation & total termination.
  - `Kernel.RngProofs`: fail-closed rejection of all-zero, all-`0xFF`, and stuck/repeating hardware RNG outputs.
  - `Kernel.VaultStoreProofs`: zero-filesystem 2-slot raw block persistence — torn-write crash consistency (`crash_consistency_torn_write`), inactive-slot targeting (`planWrite_targets_inactive`), monotonic `seq` selection (`monotonic_commit_wins`), and complete two-slot zero-wipe (`wipeBoth_erases_all`).
  - `Kernel.WireProofs`: `Op` round-trip, fail-closed CRC-32 framing, locked-state denial of all privileged ops (`locked_blocks_privileged`), and unconditional mainnet ban on host key injection (`mainnet_blocks_key_injection`).
  - `Kernel.Dwc3Proofs`: USB 2.0 Device/Configuration descriptor lengths, short SETUP packet rejection, and strict EP0 `wLength` clamping.
  - `Kernel.FbProofs` & `Kernel.GpioKeysProofs`: framebuffer coordinate/byte-offset bounds safety, multi-tick physical-button debounce (`single_glitch_never_fires`, `two_tick_glitch_never_fires`), and zero auto-repeat (`latched_never_refires`).
- **UI & Signer State Machine (`Tricorder/Proofs/{StateProofs,LayoutProofs}.lean`)**:
  - Locked/setup/wiped states carry `secrets = none`; lock/pause unconditionally clears secrets; 10 wrong PINs wipe storage; signing requires unlocked + explicitly armed review (`ARM SIGN` → `SIGN NOW`); hit-test and physical-button focus strictly target rendered buttons.

## 2. Mechanically Verified (Live Silicon, QEMU & Bitcoin Core)

- **Real Pixel 9 Pro XL (`komodo` / Tensor G4) Silicon Bring-Up**:
  - Verified live on slot `_b` (leaving slot `_a` OS intact): Cortex-X4 `MIDR=0x410FD801`, `FEAT_DIT=ON`, Stage-1 MMU + hardware `SCTLR_EL1.WXN = 1`, EL3 hardware TRNG (`ARM_SMCCC_TRNG_RND64`), live `1344×2992` DECON0 OLED + QR, debounced `GPIO_ALIVE` buttons, dual watchdog disarm, and 480 Mbps pure-Lean Synopsys DWC3 USB-C with HWACG bus-clock guard.
  - Verified live against **Bitcoin Core v32.1.0 Signet**: generated 24 words from hardware TRNG, matched Taproot 2-of-3 descriptor address byte-for-byte, physically co-signed a `1,784`-byte Taproot PSBT, finalized & mined into a real Signet block, and verified the `1,956`-byte signed PSBT QR code photographed off the OLED decodes byte-for-byte via Apple Vision.
- **Hardware MMU Protection (`scripts/qemu-checks`)**:
  - Runs 9 fault-injection tests on AArch64 Stage-1 MMU + hardware `SCTLR_EL1.WXN = 1` in `qemu-system-aarch64 -M virt -cpu max`: verifies `DIT=true`, `RNDR=true`, `FDT OK`, VirtIO-MMIO v2 discovery, and proves all 8 forbidden accesses (`write-code`, `write-constant`, `run-data`, `run-heap`, `run-stack`, `read-zero`, `overflow` onto dedicated `SP_EL1` exception stack, `beside-device`) trap cleanly in EL1 synchronous aborts.
- **Full Bare-Metal Bitcoin Core Regtest Co-Signing & Persistence (`scripts/qemu-regtest-e2e`)**:
  - Boots the bare-metal `Image` in QEMU with `ramfb` + raw 2-slot `virtio-blk` disk + `virtio-rng`, creates a PIN-locked vault, survives a **hard power-off & cold reboot**, rejects wrong PINs, unlocks with the right PIN, co-signs real **Taproot 2-of-3**, **SegWit v0 2-of-3** (with mandatory `nonWitnessUTXO` check), and **`silo/approve`** against live `bitcoind -regtest` (mined in blocks), and verifies live QEMU `ramfb` QR screenshots decode via macOS CoreImage `CIDetector`.
- **Boot Image & AVB2 Integrity (`Tests/BootImgTest.lean`)**:
  - Verifies `boot_img_hdr_v4` round-trip, RSA-4096 `avb_pkmd.bin` (1032 bytes), AVB2 `vbmeta.img` verification, and 1-byte tamper rejection on both `boot.img` and `vbmeta.img`.
- **Differential Runtime, Sanitizers & Allocator Fuzzing**:
  - `rt-test`, `big-test`, and `signer-test` produce identical output on Lean's runtime, the verified minimal runtime, and ASan+UBSan checked builds; `mini-fuzz` cross-checks thousands of random alloc/free sequences.

## 3. Trusted Computing Base (TCB) & Honest Limits

Dropping Linux and Android removes ~30 million lines of kernel, Binder, Zygote, SurfaceFlinger, libc, modem/Wi-Fi daemons, and filesystem code from the TCB. What remains trusted:

1. **Silicon & Immutable Boot ROM**: Pixel Tensor G4 SoC, Titan M2 verified boot chip, EL3 firmware (`ARM_SMCCC_TRNG_RND64`), Google ABL bootloader (which verifies `avb_custom_key` + `vbmeta.img` + `boot.img` before jumping to `_image_start`), and the OLED panel driver IC.
2. **Build Toolchain**: Lean 4 compiler, `libInit.a`/`libStd.a`, bundled `clang`/`ld.lld`, and `openssl` (host AVB2 signing).
3. **Unverified C/Asm Shim (~1,050 LOC total)**: `boot/aarch64/{entry.S,vectors.S,early.c}`, `rt/{object.c,apply.c,io.c,panic.c,extra.c}`, and `rt/bare/{libc.c,hw.c,platform.c}`. All hardware MMIO and DMA bounds checks live in `rt/bare/hw.c` (using the proved branchless `in_bounds` mask).
4. **Persistence & Physical At-Rest Security**:
   - **Stateless (RAM-only) mode on Pixel (current default)**: Zero key material ever touches UFS flash; powering off or wiping leaves zero ciphertext on disk.
   - **Optional raw 2-slot UFS persistence (tracked issue)**: When enabled, an attacker with physical UFS extraction can brute-force PBKDF2-HMAC-SHA512 (200,000 iterations) offline against the raw vault slot — use an 8–12 digit PIN.
5. **Side-Channels & Codegen**: `PSTATE.DIT = 1` + branchless `SecpCt`/`Mini.Secret` mitigate timing channels, and `Mini.Alloc` zeroes freed heap blocks, but LLVM codegen and physical EM/power probing are not machine-proved.
6. **Bootloader Relock**: Until `avb_custom_key` is flashed and `fastboot flashing lock` is run (tracked as a dedicated production ceremony issue), an attacker with physical USB-C access can flash a modified `boot_b` image.
