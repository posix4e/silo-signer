# silo-signer

The override key of a [silo](https://github.com/posix4e/silo) wallet, on a phone that runs nothing else.

silo is a co-signer for an exchange's Bitcoin hot wallet. The wallet is two of three keys: the exchange's,
silo's in an AWS Nitro Enclave, and an override key that a person holds. The exchange's key and the override
key spend without silo. That is how a payment above silo's limits is made on purpose, and how the funds come
out if the enclave is lost. This repository is the device for that third key. Its working name in the code is
"tricorder".

It is a Google Pixel 9 Pro XL with the signer as its whole software: no Android, no Linux, no C library, no
file system and no network. The signer is written in Lean 4 and runs on the minimal runtime of
[silo-os](https://github.com/posix4e/silo-os), copied here (see "The copy of silo-os" below). The same image
runs under QEMU, which is where it is tested.

## Status

- The image from this branch has run under QEMU only, where it co-signs for Taproot and SegWit v0 wallets of
  two of three keys against Bitcoin Core on regtest (`scripts/qemu-regtest-e2e`).
- An earlier image, commit `b605672`, ran on a Pixel 9 Pro XL on 2026-11-22: it made a key from the phone's
  hardware random source, and co-signed two payments from a Taproot wallet of two of three keys that a signet
  confirmed.
- An image built for mainnet from commit `519e5f0` ran on the same phone later that day. Its holder restored
  a key from 12 words on the touchscreen, accepted a SegWit v0 wallet of two of three keys, and signed one
  payment of 25,000 sats from it, which mainnet confirmed in block 977,106
  (`ad56e89c5505c7f8c457defaeef69575cd03e26edf62ecf335f9882bb317fefe`). The wallet held under 100,000 sats.
  Nothing changed after that commit has run on the phone in a signet or mainnet image.
- That is the only wallet with money in it whose key it has held, and nobody but its author has read it.
- On the Pixel the key is in memory only: switching the phone off loses it, and it comes back from its 12 or
  24 words. Keeping it on the phone's storage is written and tested under QEMU but is not safe to use yet (see
  `THREAT_MODEL.md`).
- The phone's bootloader is unlocked. Anyone holding the phone can put another image on it.

## What it does

1. Makes 24 words from the phone's hardware random source, or takes 24 words its holder enters, and derives
   one account from them: `m/86'/coin'/0'`.
2. Is shown a wallet as a descriptor, `tr(KEY, sortedmulti_a(k, …))` or `wsh(sortedmulti(k, …))`. It takes the
   wallet only if its own key is in it, at least two different keys must sign, and its holder accepts it on
   the screen, where the first address is shown to compare.
3. Is handed a payment as a PSBT. It checks every input is the wallet's (for SegWit v0, against the whole
   previous transaction), works out what leaves, and refuses a fee over a tenth of the inputs.
4. Shows the payment: what leaves, the fee, and every output with its whole address, three to a page. It can
   be armed only from the last page, and signs only on a second press after arming.
5. Gives the signed PSBT back over the cable, and as a QR code on the screen.

Nothing sent over the cable signs. While a wallet or a payment is on the screen, nothing sent over the cable
replaces it. Left unlocked and alone for about five minutes, it locks and wipes its secrets from memory.

Left alone for about a minute, locked or not, its panel goes dark. A button press or a touch lights it again
and does nothing else: a press on a dark panel is never passed on to the screen behind it. A new wallet or
payment from the cable lights it too. Going dark changes nothing about locking, and a panel lit after the
five minutes shows the lock screen. What "dark" is, exactly:

- Dark: the picture is black, which on this OLED panel is unlit pixels, and nothing is drawn until it is lit
  again. The touch controller is not read; only its interrupt line is looked at.
- Still powered: the panel's own controller, the display controller and the link between them (no display-off
  or sleep command is sent); the touch controller, which goes on scanning so that a touch can light the panel;
  USB; and the processor, at its usual speed.
- In a regtest image the processor sleeps between looks at the buttons, the glass and the cable, about 370
  times a second (`wfe`, woken by the timer's event stream). In signet and mainnet images it does not sleep:
  it spins as before. An image whose sleep did not end would be dark and deaf until switched off, and
  switching off loses the key, so the sleep was tried in a regtest image first.
- A regtest image of commit `0f631c9` ran on the Pixel on 2026-11-22. Its panel went dark a minute after the
  last press, it answered the cable through five minutes of dark and sleep, it locked itself in the dark at
  five minutes with the panel still dark, a press from the host then lit the lock screen and pressed nothing,
  and a touch lit a dark panel. How much power any of this saves has not been measured, and no signet or
  mainnet image with it has run on the phone.

## What is proved, and what is not

`lake build TricorderGate` fails if any theorem named in `Tricorder/Gate.lean` has an unproved step or depends
on an axiom beyond Lean's three (`propext`, `Quot.sound`, `Classical.choice`).

Proved:

- The signing code (`SecpCt`, from [winnow-lean](https://github.com/winnowwallet/winnow-lean) at `v0.9.27`)
  signs what the plain reference signs, and a signature it checks is a valid one.
- The screens, as a state machine (`Tricorder/Proofs/StateProofs.lean`): a signature is asked for only by the
  confirm button, unlocked, on an armed payment, and for that payment; arming happens only from the last page
  of the outputs; a payment that arrives starts unarmed at the first page; locking wipes the secrets.
- A text no longer than the lines it is given is shown whole (`wrapChars_complete`), which is what the address
  lines rely on; a press lands on the button that is drawn there (`LayoutProofs.lean`).
- The rules for the cable (`Kernel/WireProofs.lean`): locked, nothing private is answered; while reviewing,
  nothing is replaced; only a regtest build lets the host press the buttons.
- Smaller facts about the page tables, the device-tree header, the storage slots, the frame buffer's bounds and
  the buttons' debounce (`Kernel/*Proofs.lean`), about going dark (`Kernel/IdleProofs.lean`: a dark panel
  passes no press on, any press lights it, and the lock is decided as if the panel were lit), and about the runtime's allocator and big numbers (`Mini/`,
  `Runtime/`).

Not proved:

- That what is drawn is what was reviewed: the theorems are about the state machine and the layout, and the
  drawing code between them is tested (`Tests/JourneyTest.lean` reads the addresses off the drawn screen).
- That the firmware runs the state machine as written: `Tricorder/OsMain.lean`, the drivers and the boot code
  are tested, under QEMU and on the phone, and not proved.
- The review of a payment (`Tricorder/Signer/Review.lean`) and the wallet code under it, which is winnow's.
- About 2,400 lines of C and assembly in `boot/aarch64/` and `rt/`.
- Some proofs copied from silo-os use `bv_decide` (`Mini/WordProofs.lean`, `Runtime/Utf8Proofs.lean`). They are
  built, and are not among the gated theorems.

## Layout

```text
Tricorder/   Keys and the vault (Crypto/), wallets, review and signing (Signer/), the QR encoder (Qr/),
             the screens (Ui/), their proofs (Proofs/), the gate (Gate.lean), the firmware's main loop (OsMain.lean)
Kernel/      Page tables, device tree, entropy, storage slots, the cable's frames, USB, frame buffer, buttons,
             the touchscreen, going dark when left alone
MkBoot/      The boot image and its signature, made in Lean
boot/, rt/   Boot code, and the runtime's C
Mini/, Runtime/   The runtime's Lean, from silo-os
Tests/       signer-test, journey-test, regtest-cli, boot-img-test
scripts/     build-bare, qemu-checks, qemu-regtest-e2e, regtest-e2e, flash-komodo
tools/       tricorder_usb.c, the command line for the cable on macOS
```

## Building and testing

The Lean toolchain is named in `lean-toolchain`. The images also need Lean's AArch64 libraries in
`~/.elan/cross/` (or at `TRICORDER_ARM64_TOOLCHAIN`), `qemu-system-aarch64`, and for the runs against Bitcoin
Core `bitcoind` and `bitcoin-cli`.

```bash
lake build                          # everything, the proof gate included
.lake/build/bin/signer-test         # keys, vault, review, signing
.lake/build/bin/journey-test        # every screen by its buttons, to a signed payment
.lake/build/bin/boot-img-test       # the boot image and its signature

scripts/build-min regtest-cli && scripts/regtest-e2e      # the signer as a process, against Bitcoin Core
scripts/build-bare probe qemu regtest && scripts/qemu-checks       # nine things the memory layout must refuse
scripts/build-bare os qemu regtest && scripts/qemu-regtest-e2e     # the image under QEMU, against Bitcoin Core
```

`scripts/qemu-regtest-e2e` drives the image by the cable's frames. In a regtest build the host may press the
buttons, which is how the script gets through the screens. In a signet or mainnet build that frame is refused.

## On the Pixel

```bash
scripts/build-bare os komodo signet
scripts/flash-komodo slot-b os signet
clang -O2 -Wall -Wextra -framework IOKit -framework CoreFoundation -o build/tricorder-usb tools/tricorder_usb.c
```

`flash-komodo` writes slot `_b` only and leaves the phone's own system in slot `_a`. `build-bare` makes a
signing key for the image in `build/avb-keys/` the first time; `build/` is not in the repository.

```bash
build/tricorder-usb ping
build/tricorder-usb keys                        # refused while locked
build/tricorder-usb push-descriptor wallet.txt  # the wallet, for its holder to accept on the screen
build/tricorder-usb push-override payment.psbt  # a payment, for its holder to read, arm and sign
build/tricorder-usb poll                        # the signed payment, once it is signed
```

The live demo page in [silo-site](https://github.com/posix4e/silo-site) speaks the same frames from the browser
over WebUSB. Its test runs `regtest-cli` as the override key of the wallet silo's `scripts/live-signer start`
makes, of both kinds. The page has been run against a stand-in for the device, not against the Pixel.

## The copy of silo-os

`Mini/`, `Runtime/`, `fuzz/` and most of `rt/` are silo-os's, copied in November 2026 and not a dependency, so
they will drift. `rt/bare/` and `Kernel/Hw.lean` differ from silo-os's because the machine does.

See `THREAT_MODEL.md` for who it is meant to stand against and where it does not.

## License

Licensed under the GNU Affero General Public License, version 3 ([LICENSE](LICENSE)).
