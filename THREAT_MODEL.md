# Threat model

What silo-signer is meant to stand against, what it rests on, and where it does not hold. `README.md` says
what is proved and what is only tested.

## What it is for

A silo wallet is two of three keys. The exchange's server holds the use of one. This device holds another, the
override key, and its holder is the person who decides whether a payment above silo's limits is made. The
attacker it is built against holds the exchange's server: they prepare the payment, they are on the other end
of the cable, and they want a signature on something its holder did not agree to.

So the device takes nothing on trust from the cable. What it shows is worked out on the device from the bytes
it was sent, and what it signs is what it showed.

## What the attacker on the cable can do

- **Send any bytes.** A frame is checked for its length and CRC, a PSBT is parsed in Lean, and a payment that
  is not this wallet's, or whose fee is over a tenth of its inputs, is refused before anything is shown.
- **Ask for a signature.** There is no such frame. A payment is put on the screen, and its holder arms and
  confirms with the buttons (`sign_requires_armed_review`).
- **Hide an output, or part of an address.** Every output is on a page, with its whole address, and the signer
  is armed only from the last page (`arming_requires_last_page`, `wrapChars_complete`). The drawing itself is
  tested, not proved.
- **Swap the payment once it has been read.** While a wallet or a payment is on the screen, a frame that would
  put another in its place is refused (`reviewing_blocks_push`). Its holder answers on the device first.
- **Offer another wallet.** A wallet is taken only if this device's key is in it and at least two different
  keys must sign, and only when its holder accepts it on the screen. The screen shows the first address. The
  holder has to compare it with the wallet they mean: the device cannot know which wallet that is.
- **Read the result of an earlier signing as this one's.** What was signed before is forgotten when a new
  payment arrives.
- **Press the buttons.** Only in an image built for regtest, which the tests need. In a signet or mainnet
  image that frame is refused (`only_test_builds_inject_keys`).
- **Read and write the phone's registers.** Only in an image built for regtest, where it is how new hardware
  is brought up from the host (`tools/bench/`), and only inside the register windows the image maps. In a
  signet or mainnet image that frame is refused (`only_test_builds_touch_registers`).

## What it rests on

- **The phone.** Its processor, its boot ROM and bootloader, the firmware below the signer that answers the
  request for random numbers, and the display. None of it is ours, and the signer cannot check it.
- **One source of randomness for the key.** The 24 words come from the phone's hardware random source, put
  through SHA-256, after a check that refuses only the plainest failures: all zeros, all ones, a repeated
  word. A source that is wrong in a less obvious way would not be caught. A holder who does not want to rest
  on it enters 24 words of their own. Signatures do not rest on it alone: each nonce is made from the key, the
  message and the fresh bytes together.
- **The build.** Lean's compiler and libraries, clang and lld, and openssl for the image's signature.
- **The code that is not proved** (`README.md`): the review of a payment, the drawing, the main loop, the
  drivers, and about 2,400 lines of C and assembly.
- **Its holder.** They read the screen, compare the address, and keep the 24 words.

## Where it does not hold

- **Someone who holds the phone.** The bootloader is unlocked, so they can flash an image of their own, and a
  holder who then enters their words gives them the key. Locking the bootloader to our own signing key is not
  done (issue 5).
- **The key kept on the phone's storage.** On the Pixel the key is in memory only, and this does not arise.
  The code to keep it on storage exists and runs under QEMU. It encrypts the words under a PIN of 6 to 12
  digits with PBKDF2-HMAC-SHA512 at 4,096 rounds, and nothing ties the key to the phone. Whoever copies the
  storage tries every 6-digit PIN in minutes, and the count of wrong PINs does not bind them. It must not be
  used on a real phone until the key is tied to hardware that limits guesses. Against someone using the
  device itself, the count holds: an attempt is counted on storage before the PIN is tried, a PIN is not
  tried if it cannot be counted, and the tenth wrong one wipes both slots.
- **A device left unlocked.** It locks itself after about five minutes without a button press, and at once
  from its lock button. In between, whoever picks it up can sign what the cable offers.
- **Side channels beyond timing.** The signing code does not branch on a secret or use one as an address, and
  the processor's data-independent timing mode is on. Power and electromagnetic measurement by someone with
  the phone on a bench are not addressed. That the compiler kept the code free of secret-dependent branches is
  checked for silo's build of the same signing code, not for this one.
- **A regtest image.** The host can press its buttons, and read and write its registers. It is for tests and
  the bench, and holds nothing of value.
- **Long payments over the cable.** One frame is at most 4,096 bytes over USB. A payment that does not fit is
  refused, not cut short.
