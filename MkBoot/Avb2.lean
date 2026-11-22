import Winnow.Crypto.Sha2

/-! # Pure-Lean Android Verified Boot 2.0 (`MkBoot.Avb2`)

Implements AOSP's AVB 2.0 (`libavb`) structures in pure Lean + `openssl` (zero Python `avbtool`):
1. **`avb_pkmd.bin`** (`AvbRSAPublicKeyHeader` for `fastboot flash avb_custom_key`): computes exact
   RSA-4096 Montgomery constants `n0inv = (-n⁻¹) mod 2³²` and `R² = 2^(2·4096) mod n` in Lean `Nat`.
2. **`AvbVBMetaImageHeader`** (`"AVB0"`, 256-byte big-endian header) + RSA-4096 SHA-256 signature
   (`AVB_ALGORITHM_TYPE_SHA256_RSA4096 = 2`) + `AvbHashDescriptor` for the `boot` partition.
3. **`verifyVbmeta`**: independently recomputes and checks the AVB2 `vbmeta.img` signature AND
   verifies the `boot.img` SHA-256 digest against the signed `AvbHashDescriptor`! -/

namespace MkBoot.Avb2

def vbmetaMagic : ByteArray := "AVB0".toUTF8
def footerMagic : ByteArray := "AVBf".toUTF8
def algSha256Rsa4096 : Nat := 2
def vbmetaHeaderSize : Nat := 256
def rsa4096Bits : Nat := 4096
def rsa4096Bytes : Nat := 512

private def pushBe32 (b : ByteArray) (v : Nat) : ByteArray :=
  b.push ((v >>> 24) &&& 0xff).toUInt8
   |>.push ((v >>> 16) &&& 0xff).toUInt8
   |>.push ((v >>> 8) &&& 0xff).toUInt8
   |>.push (v &&& 0xff).toUInt8

private def pushBe64 (b : ByteArray) (v : Nat) : ByteArray :=
  pushBe32 (pushBe32 b (v >>> 32)) (v &&& 0xffffffff)

def readBe32 (b : ByteArray) (off : Nat) : Nat :=
  if off + 4 ≤ b.size then
    ((b.get! off).toNat <<< 24) |||
    ((b.get! (off + 1)).toNat <<< 16) |||
    ((b.get! (off + 2)).toNat <<< 8) |||
    (b.get! (off + 3)).toNat
  else 0

def readBe64 (b : ByteArray) (off : Nat) : Nat :=
  (readBe32 b off <<< 32) ||| readBe32 b (off + 4)

private def align64 (n : Nat) : Nat := ((n + 63) / 64) * 64
private def padZeros (b : ByteArray) (target : Nat) : ByteArray :=
  if b.size ≥ target then b else b ++ ByteArray.mk (Array.replicate (target - b.size) 0)

private def natToBeBytes (n len : Nat) : ByteArray := Id.run do
  let mut out := Array.replicate len (0 : UInt8)
  let mut v := n
  for i in [0:len] do
    out := out.set! (len - 1 - i) (v &&& 0xff).toUInt8
    v := v >>> 8
  return ByteArray.mk out

private def hexDigitVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

private def parseHexNat (s : String) : Except String Nat := do
  let mut acc := 0
  for c in s.toList do
    if c == ':' || c == '\n' || c == '\r' || c == ' ' then continue
    let some d := hexDigitVal? c | throw s!"invalid hex char '{c}'"
    acc := acc * 16 + d
  return acc

/-- Computes `(-n⁻¹) mod 2^32` using Newton-Raphson Hensel lifting (5 iterations suffices for 32 bits). -/
def computeN0Inv (n : Nat) : Nat := Id.run do
  let base := 1 <<< 32
  let mut inv : Nat := 1
  for _ in [0:5] do
    inv := (inv * (2 + base - ((n * inv) % base))) % base
  return (base - inv) % base

/-- Modular squaring helper `a^e mod m`. -/
def modPow (a e m : Nat) : Nat := Id.run do
  let mut res := 1 % m
  let mut base := a % m
  let mut exp := e
  while exp > 0 do
    if exp % 2 == 1 then res := (res * base) % m
    base := (base * base) % m
    exp := exp / 2
  return res

/-- Extracts the RSA-4096 modulus `n` from a PEM private key using `openssl rsa -modulus -noout`
and encodes AOSP's exact `avb_pkmd.bin` (`AvbRSAPublicKeyHeader || n || R² mod n`). -/
def buildAvbPublicKey (rsaKeyPem : String) : IO ByteArray := do
  let out ← IO.Process.output {
    cmd := "openssl"
    args := #["rsa", "-in", rsaKeyPem, "-modulus", "-noout"]
  }
  if out.exitCode != 0 then throw <| IO.userError s!"openssl rsa -modulus failed: {out.stderr}"
  let line := out.stdout.trimAscii.toString
  let hex := match line.splitOn "=" with
    | [_, h] => h
    | _ => line
  let n ← IO.ofExcept (parseHexNat hex)
  let n0inv := computeN0Inv n
  let r := modPow 2 rsa4096Bits n
  let rr := (r * r) % n
  let hdr := pushBe32 (pushBe32 ByteArray.empty rsa4096Bits) n0inv
  return hdr ++ natToBeBytes n rsa4096Bytes ++ natToBeBytes rr rsa4096Bytes

/-- Signs `data` with RSA-4096 SHA-256 PKCS#1 v1.5 via `openssl dgst -sha256 -sign`. -/
private def opensslRsaSign (rsaKeyPem : String) (data : ByteArray) : IO ByteArray := do
  let tmpIn := "/tmp/tricorder-avb2-in.bin"
  let tmpSig := "/tmp/tricorder-avb2-sig.bin"
  IO.FS.writeBinFile tmpIn data
  let out ← IO.Process.output {
    cmd := "openssl"
    args := #["dgst", "-sha256", "-sign", rsaKeyPem, "-out", tmpSig, tmpIn]
  }
  if out.exitCode != 0 then throw <| IO.userError s!"openssl avb2 sign failed: {out.stderr}"
  let sig ← IO.FS.readBinFile tmpSig
  try IO.FS.removeFile tmpIn catch _ => pure ()
  try IO.FS.removeFile tmpSig catch _ => pure ()
  return sig

/-- Verifies an RSA-4096 SHA-256 signature against a PEM public key extracted from `rsaKeyPem` or pubPem. -/
private def opensslRsaVerify (pubPem : String) (data sig : ByteArray) : IO Bool := do
  let tmpIn := "/tmp/tricorder-avb2-vin.bin"
  let tmpSig := "/tmp/tricorder-avb2-vsig.bin"
  IO.FS.writeBinFile tmpIn data
  IO.FS.writeBinFile tmpSig sig
  let out ← IO.Process.output {
    cmd := "openssl"
    args := #["dgst", "-sha256", "-verify", pubPem, "-signature", tmpSig, tmpIn]
  }
  try IO.FS.removeFile tmpIn catch _ => pure ()
  try IO.FS.removeFile tmpSig catch _ => pure ()
  return out.exitCode == 0

/-- Encodes one AOSP `AvbHashDescriptor` (tag = 2) for a partition (`boot`) with SHA-256 digest. -/
def encodeHashDescriptor (partName : String) (imageSize : Nat) (salt digest : ByteArray) : ByteArray :=
  let algBytes := padZeros "sha256".toUTF8 32
  let nameBytes := partName.toUTF8
  let body :=
    pushBe64 ByteArray.empty imageSize ++
    algBytes ++
    pushBe32 ByteArray.empty nameBytes.size ++
    pushBe32 ByteArray.empty salt.size ++
    pushBe32 ByteArray.empty digest.size ++
    pushBe32 ByteArray.empty 0 ++ -- flags
    ByteArray.mk (Array.replicate 60 0) ++ -- reserved[60]
    nameBytes ++ salt ++ digest
  let paddedLen := ((body.size + 7) / 8) * 8
  let bodyPadded := padZeros body paddedLen
  pushBe64 (pushBe64 ByteArray.empty 2) bodyPadded.size ++ bodyPadded

/-- Builds a complete signed AVB2 `vbmeta.img` covering `bootImg` (`partName = "boot"`) plus `avb_pkmd.bin`. -/
def signVbmeta (partName : String) (bootImg : ByteArray) (rsaKeyPem : String) : IO (ByteArray × ByteArray) := do
  let pkmd ← buildAvbPublicKey rsaKeyPem
  let salt := Winnow.sha256 "TRICORDER-AVB2-SALT".toUTF8 |>.extract 0 16
  let digest := Winnow.sha256 (salt ++ bootImg)
  let desc := encodeHashDescriptor partName bootImg.size salt digest
  -- Auxiliary block: descriptors || public_key (avb_pkmd) || public_key_metadata (empty), 64-byte aligned.
  let descOff := 0
  let descSize := desc.size
  let pkOff := descSize
  let pkSize := pkmd.size
  let auxRaw := desc ++ pkmd
  let auxSize := align64 auxRaw.size
  let aux := padZeros auxRaw auxSize

  -- Authentication block: hash (32B) || signature (512B), 64-byte aligned.
  let hashOff := 0
  let hashSize := 32
  let sigOff := 32
  let sigSize := rsa4096Bytes
  let authSize := align64 (hashSize + sigSize)

  -- Build 256-byte big-endian AvbVBMetaImageHeader
  let mut hdr := vbmetaMagic
  hdr := pushBe32 hdr 1 -- required_libavb_version_major = 1
  hdr := pushBe32 hdr 0 -- required_libavb_version_minor = 0
  hdr := pushBe64 hdr authSize
  hdr := pushBe64 hdr auxSize
  hdr := pushBe32 hdr algSha256Rsa4096
  hdr := pushBe64 hdr hashOff
  hdr := pushBe64 hdr hashSize
  hdr := pushBe64 hdr sigOff
  hdr := pushBe64 hdr sigSize
  hdr := pushBe64 hdr pkOff
  hdr := pushBe64 hdr pkSize
  hdr := pushBe64 hdr 0 -- pk_metadata_offset
  hdr := pushBe64 hdr 0 -- pk_metadata_size
  hdr := pushBe64 hdr descOff
  hdr := pushBe64 hdr descSize
  hdr := pushBe64 hdr 0 -- rollback_index
  hdr := pushBe32 hdr 0 -- flags
  hdr := pushBe32 hdr 0 -- rollback_index_location
  hdr := hdr ++ padZeros "tricorder-mkboot 0.1".toUTF8 48
  hdr := padZeros hdr vbmetaHeaderSize

  -- AVB2 authenticates `header || aux`
  let toAuth := hdr ++ aux
  let authHash := Winnow.sha256 toAuth
  let sig ← opensslRsaSign rsaKeyPem toAuth
  if sig.size != rsa4096Bytes then
    throw <| IO.userError s!"expected 512-byte RSA-4096 signature, got {sig.size}"
  let auth := padZeros (authHash ++ sig) authSize
  let vbmeta := padZeros (hdr ++ auth ++ aux) (align64 (hdr.size + auth.size + aux.size))
  return (vbmeta, pkmd)

/-- Verifies a signed AVB2 `vbmeta.img` against `bootImg` and `pubPem` (checks magic, header hash,
RSA-4096 signature, and `AvbHashDescriptor` digest of `bootImg`). -/
def verifyVbmeta (vbmeta bootImg : ByteArray) (pubPem : String) : IO (Except String String) := do
  if vbmeta.size < vbmetaHeaderSize then return .error "vbmeta shorter than 256-byte header"
  if vbmeta.extract 0 4 != vbmetaMagic then return .error "vbmeta missing AVB0 magic"
  let authSize := readBe64 vbmeta 12
  let auxSize := readBe64 vbmeta 20
  let alg := readBe32 vbmeta 28
  if alg != algSha256Rsa4096 then return .error s!"unexpected AVB2 algorithm {alg}"
  let hashOff := readBe64 vbmeta 32
  let hashSize := readBe64 vbmeta 40
  let sigOff := readBe64 vbmeta 48
  let sigSize := readBe64 vbmeta 56
  let descOff := readBe64 vbmeta 96
  let descSize := readBe64 vbmeta 104
  if vbmetaHeaderSize + authSize + auxSize > vbmeta.size then
    return .error "vbmeta auth/aux blocks exceed image size"
  let hdr := vbmeta.extract 0 vbmetaHeaderSize
  let auth := vbmeta.extract vbmetaHeaderSize (vbmetaHeaderSize + authSize)
  let aux := vbmeta.extract (vbmetaHeaderSize + authSize) (vbmetaHeaderSize + authSize + auxSize)
  let toAuth := hdr ++ aux
  let storedHash := auth.extract hashOff (hashOff + hashSize)
  if Winnow.sha256 toAuth != storedHash then
    return .error "vbmeta SHA-256 header+aux hash mismatch"
  let sig := auth.extract sigOff (sigOff + sigSize)
  let ok ← opensslRsaVerify pubPem toAuth sig
  if !ok then return .error "vbmeta RSA-4096 signature verification FAILED"
  -- Verify AvbHashDescriptor (tag 2) inside aux matches `bootImg`
  if descOff + descSize > aux.size || descSize < 16 + 116 then
    return .error "vbmeta missing/truncated hash descriptor"
  let desc := aux.extract descOff (descOff + descSize)
  let tag := readBe64 desc 0
  if tag != 2 then return .error s!"unexpected descriptor tag {tag}"
  let expectedImgSize := readBe64 desc 16
  let nameLen := readBe32 desc 56
  let saltLen := readBe32 desc 60
  let digLen := readBe32 desc 64
  if expectedImgSize != bootImg.size then
    return .error s!"boot.img size mismatch: descriptor={expectedImgSize}, actual={bootImg.size}"
  let dataStart := 16 + 116
  let salt := desc.extract (dataStart + nameLen) (dataStart + nameLen + saltLen)
  let wantDigest := desc.extract (dataStart + nameLen + saltLen) (dataStart + nameLen + saltLen + digLen)
  let actualDigest := Winnow.sha256 (salt ++ bootImg)
  if actualDigest != wantDigest then
    return .error "boot.img SHA-256 digest does not match signed vbmeta AvbHashDescriptor"
  return .ok s!"AVB2 OK: RSA-4096 verified, boot.img ({bootImg.size}B) SHA-256 matches signed vbmeta"

end MkBoot.Avb2
