/-! # Pure-Lean Android `boot_img_hdr_v4` Packager & Verifier (`MkBoot.BootImg`)

Implements AOSP's exact `boot_img_hdr_v4` (`1584`-byte header padded to `4096` bytes + page-aligned
ARM64 kernel `Image`, zero Linux ramdisk) required by Pixel 9 Pro XL (`komodo`) ABL. -/

namespace MkBoot.BootImg

def bootMagic : ByteArray := "ANDROID!".toUTF8
def headerSizeV4 : Nat := 1584
def pageSize : Nat := 4096
def cmdlineSize : Nat := 1536

private def alignUp (n align : Nat) : Nat :=
  ((n + align - 1) / align) * align

private def putU32LeAt (a : Array UInt8) (off v : Nat) : Array UInt8 :=
  a.set! off (v &&& 0xff).toUInt8
   |>.set! (off + 1) ((v >>> 8) &&& 0xff).toUInt8
   |>.set! (off + 2) ((v >>> 16) &&& 0xff).toUInt8
   |>.set! (off + 3) ((v >>> 24) &&& 0xff).toUInt8

def readU32Le (b : ByteArray) (off : Nat) : Nat :=
  if off + 4 ≤ b.size then
    (b.get! off).toNat |||
    ((b.get! (off + 1)).toNat <<< 8) |||
    ((b.get! (off + 2)).toNat <<< 16) |||
    ((b.get! (off + 3)).toNat <<< 24)
  else 0

private def copyInto (dst : Array UInt8) (off : Nat) (src : ByteArray) : Array UInt8 := Id.run do
  let mut out := dst
  let lim := min src.size (out.size - off)
  for i in [0:lim] do
    out := out.set! (off + i) (src.get! i)
  return out

/-- Encodes Android `os_version` field: `(major << 14 | minor << 7 | patch) << 11 | ((year - 2000) << 4 | month)`. -/
def encodeOsVersion (major minor patch year month : Nat) : Nat :=
  let ver := (major <<< 14) ||| (minor <<< 7) ||| patch
  let lvl := ((year - 2000) <<< 4) ||| month
  (ver <<< 11) ||| lvl

structure BootImgV4 where
  kernel : ByteArray
  ramdisk : ByteArray := ByteArray.empty
  cmdline : String := ""
  osVersion : Nat := encodeOsVersion 15 0 0 2026 11
  deriving BEq, Inhabited

/-- Packs a `BootImgV4` into exact page-aligned AOSP `boot_img_hdr_v4` bytes. -/
def packV4 (cfg : BootImgV4) : ByteArray :=
  let hdr := Array.replicate pageSize (0 : UInt8)
  let hdr := copyInto hdr 0 bootMagic
  let hdr := putU32LeAt hdr 8 cfg.kernel.size
  let hdr := putU32LeAt hdr 12 cfg.ramdisk.size
  let hdr := putU32LeAt hdr 16 cfg.osVersion
  let hdr := putU32LeAt hdr 20 headerSizeV4
  let hdr := putU32LeAt hdr 40 4 -- header_version = 4
  let cmdBytes := cfg.cmdline.toUTF8
  let cmdTrim := if cmdBytes.size < cmdlineSize then cmdBytes else cmdBytes.extract 0 (cmdlineSize - 1)
  let hdr := copyInto hdr 44 cmdTrim
  let hdr := putU32LeAt hdr 1580 0 -- signature_size = 0 (AVB2 footer used)
  let kPad := alignUp cfg.kernel.size pageSize - cfg.kernel.size
  let rPad := alignUp cfg.ramdisk.size pageSize - cfg.ramdisk.size
  ByteArray.mk hdr ++
    cfg.kernel ++ ByteArray.mk (Array.replicate kPad 0) ++
    cfg.ramdisk ++ ByteArray.mk (Array.replicate rPad 0)

/-- Parses & validates an AOSP `boot_img_hdr_v4` image, extracting the kernel `Image` and cmdline. -/
def parseV4 (raw : ByteArray) : Except String BootImgV4 := do
  if raw.size < pageSize then throw "boot.img shorter than 4096-byte header page"
  if raw.extract 0 8 != bootMagic then throw "boot.img missing ANDROID! magic"
  let hdrVer := readU32Le raw 40
  if hdrVer != 4 then throw s!"expected boot_img_hdr_v4, got v{hdrVer}"
  let hdrSz := readU32Le raw 20
  if hdrSz != headerSizeV4 then throw s!"unexpected v4 header_size {hdrSz}"
  let kSize := readU32Le raw 8
  let rSize := readU32Le raw 12
  let osVersion := readU32Le raw 16
  let kPages := alignUp kSize pageSize
  let rPages := alignUp rSize pageSize
  if pageSize + kPages + rPages > raw.size then throw "boot.img truncated kernel/ramdisk"
  let kernel := raw.extract pageSize (pageSize + kSize)
  let ramdisk := raw.extract (pageSize + kPages) (pageSize + kPages + rSize)
  -- Read NUL-terminated cmdline
  let mut cmdArr : Array UInt8 := #[]
  for i in [0:cmdlineSize] do
    let c := raw.get! (44 + i)
    if c == 0 then break
    cmdArr := cmdArr.push c
  let cmdline := String.fromUTF8! (ByteArray.mk cmdArr)
  return { kernel, ramdisk, cmdline, osVersion }

end MkBoot.BootImg
