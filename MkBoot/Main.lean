import MkBoot.ElfToImage
import MkBoot.BootImg
import MkBoot.Avb2

/-! # Pure-Lean Bare-Metal Image & AVB2 Packager CLI (`mkboot`)

Subcommands:
- `mkboot image <in.elf> <out.Image>`
  Flattens an AArch64 ELF executable into a raw Linux ARM64 `Image` (zero `objcopy`).
- `mkboot pack <in.Image> <key.pem> <pub.pem> <out-boot.img> <out-vbmeta.img> <out-avb_pkmd.bin> [cmdline]`
  Packs AOSP `boot_img_hdr_v4`, signs AVB2 `vbmeta.img` + `avb_pkmd.bin`, and cryptographically
  self-verifies every invariant! -/

open MkBoot

def main (args : List String) : IO UInt32 := do
  match args with
  | ["image", elfPath, outPath] =>
    let elf ← IO.FS.readBinFile elfPath
    match ElfToImage.flatten elf with
    | .error e =>
      IO.eprintln s!"mkboot image FAILED: {e}"
      return 1
    | .ok img =>
      IO.FS.writeBinFile outPath img
      IO.println s!"mkboot: wrote flat ARM64 Image {outPath} ({img.size} bytes, ARM\\x64 header verified)"
      return 0
  | "pack" :: imgPath :: keyPem :: pubPem :: bootOut :: vbmetaOut :: pkmdOut :: rest =>
    let cmdline := String.intercalate " " rest
    let kernel ← IO.FS.readBinFile imgPath
    let bootImg := BootImg.packV4 { kernel, cmdline }
    match BootImg.parseV4 bootImg with
    | .error e =>
      IO.eprintln s!"mkboot boot.img self-check FAILED: {e}"
      return 1
    | .ok _ => pure ()
    let (vbmeta, pkmd) ← Avb2.signVbmeta "boot" bootImg keyPem
    match ← Avb2.verifyVbmeta vbmeta bootImg pubPem with
    | .error e =>
      IO.eprintln s!"mkboot AVB2 self-verify FAILED: {e}"
      return 1
    | .ok msg =>
      IO.FS.writeBinFile bootOut bootImg
      IO.FS.writeBinFile vbmetaOut vbmeta
      IO.FS.writeBinFile pkmdOut pkmd
      IO.println s!"mkboot: {msg}"
      IO.println s!"mkboot: wrote {bootOut} ({bootImg.size}B), {vbmetaOut} ({vbmeta.size}B), {pkmdOut} ({pkmd.size}B)"
      return 0
  | _ =>
    IO.eprintln "usage:"
    IO.eprintln "  mkboot image <in.elf> <out.Image>"
    IO.eprintln "  mkboot pack <in.Image> <key.pem> <pub.pem> <boot.img> <vbmeta.img> <avb_pkmd.bin> [cmdline]"
    return 2
