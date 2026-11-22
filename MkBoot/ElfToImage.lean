/-! # Pure-Lean ELF64 AArch64 -> Flat ARM64 Linux `Image` Flattener (`MkBoot.ElfToImage`)

Extracts every `PT_LOAD` segment of our linked bare-metal AArch64 ELF directly into a flat raw
ARM64 Linux `Image` binary (zero GNU `objcopy` dependency) and verifies the 64-byte ARM64 Linux
boot header (`"ARM\x64"` magic at offset `0x38`). -/

namespace MkBoot.ElfToImage

def readU16Le (b : ByteArray) (off : Nat) : Nat :=
  if off + 2 ≤ b.size then
    (b.get! off).toNat ||| ((b.get! (off + 1)).toNat <<< 8)
  else 0

def readU32Le (b : ByteArray) (off : Nat) : Nat :=
  if off + 4 ≤ b.size then
    (b.get! off).toNat |||
    ((b.get! (off + 1)).toNat <<< 8) |||
    ((b.get! (off + 2)).toNat <<< 16) |||
    ((b.get! (off + 3)).toNat <<< 24)
  else 0

def readU64Le (b : ByteArray) (off : Nat) : Nat :=
  readU32Le b off ||| (readU32Le b (off + 4) <<< 32)

structure ProgramHeader where
  pType : Nat
  pFlags : Nat
  pOffset : Nat
  pVaddr : Nat
  pFilesz : Nat
  pMemsz : Nat
  deriving Repr, Inhabited

/-- Converts an ELF64 AArch64 static executable into a flat raw ARM64 Linux `Image` binary. -/
def flatten (elf : ByteArray) : Except String ByteArray := do
  if elf.size < 64 then throw "ELF too short"
  if readU32Le elf 0 != 0x464c457f then throw "not an ELF file"
  if elf.get! 4 != 2 || elf.get! 5 != 1 then throw "not 64-bit little-endian ELF"
  if readU16Le elf 18 != 183 then throw "not EM_AARCH64 (183)"
  let phoff := readU64Le elf 32
  let phentsize := readU16Le elf 54
  let phnum := readU16Le elf 56
  if phentsize < 56 || phoff + phnum * phentsize > elf.size then
    throw "ELF program headers out of bounds"
  let mut loads : Array ProgramHeader := #[]
  for i in [0:phnum] do
    let at' := phoff + i * phentsize
    let ph : ProgramHeader := {
      pType := readU32Le elf at'
      pFlags := readU32Le elf (at' + 4)
      pOffset := readU64Le elf (at' + 8)
      pVaddr := readU64Le elf (at' + 16)
      pFilesz := readU64Le elf (at' + 32)
      pMemsz := readU64Le elf (at' + 40)
    }
    if ph.pType == 1 && ph.pFilesz > 0 then
      if ph.pOffset + ph.pFilesz > elf.size then throw "PT_LOAD segment out of ELF file bounds"
      loads := loads.push ph
  if loads.size == 0 then throw "ELF contains no non-empty PT_LOAD segments"
  let mut baseVaddr := loads[0]!.pVaddr
  let mut endVaddr := loads[0]!.pVaddr + loads[0]!.pFilesz
  for ph in loads do
    if ph.pVaddr < baseVaddr then baseVaddr := ph.pVaddr
    if ph.pVaddr + ph.pFilesz > endVaddr then endVaddr := ph.pVaddr + ph.pFilesz
  let totalSize := endVaddr - baseVaddr
  if totalSize < 64 || totalSize > 64 * 1024 * 1024 then
    throw s!"flat ARM64 Image size out of range: {totalSize}"
  let mut out := Array.replicate totalSize (0 : UInt8)
  for ph in loads do
    let dstOff := ph.pVaddr - baseVaddr
    for k in [0:ph.pFilesz] do
      out := out.set! (dstOff + k) (elf.get! (ph.pOffset + k))
  let img := ByteArray.mk out
  -- Verify standard Linux ARM64 Image magic "ARM\x64" (0x644d5241) at offset 0x38
  if readU32Le img 0x38 != 0x644d5241 then
    throw "flattened Image missing ARM\\x64 magic at offset 0x38"
  return img

end MkBoot.ElfToImage
