/-! # Pure-Lean Flattened Device Tree (DTB / FDT v17) Parser (`Kernel.Fdt`)

Zero-C, bounded, total parser for the standard Flattened Device Tree (`0xd00dfeed`) handed to an
AArch64 kernel in `x0` by both QEMU `-M virt` and Pixel 9 ABL.

Extracts:
- `/memory` physical RAM ranges;
- `/chosen/bootargs` command line string;
- device nodes (`name`, `compatible`, `reg` pairs) for VirtIO-MMIO, PL011 UART, `fw_cfg`,
  `simple-framebuffer` / `cont_splash`, Exynos DECON, `gpio-keys`, `exynos-ufs`, `dwc3`, and WDT.

Proved header validation & termination properties live in `Kernel/FdtProofs.lean`. -/

namespace Kernel.Fdt

def fdtMagic : UInt32 := 0xd00dfeed
def fdtBeginNode : UInt32 := 1
def fdtEndNode : UInt32 := 2
def fdtProp : UInt32 := 3
def fdtNop : UInt32 := 4
def fdtEnd : UInt32 := 9

def readBe32 (b : ByteArray) (off : Nat) : UInt32 :=
  if off + 4 ≤ b.size then
    (b.get! off).toUInt32 <<< 24 |||
    (b.get! (off + 1)).toUInt32 <<< 16 |||
    (b.get! (off + 2)).toUInt32 <<< 8 |||
    (b.get! (off + 3)).toUInt32
  else 0

def readBe64 (b : ByteArray) (off : Nat) : UInt64 :=
  ((readBe32 b off).toUInt64 <<< 32) ||| (readBe32 b (off + 4)).toUInt64

def align4 (n : Nat) : Nat := ((n + 3) / 4) * 4

/-- Reads a NUL-terminated ASCII/UTF-8 string starting at `off`, bounded by `maxLen`. -/
def readCStr (b : ByteArray) (off : Nat) (maxLen : Nat := 256) : String × Nat := Id.run do
  let mut i := off
  let lim := min b.size (off + maxLen)
  let mut chars : Array UInt8 := #[]
  while i < lim do
    let c := b.get! i
    if c == 0 then
      return (String.fromUTF8! (ByteArray.mk chars), i + 1)
    chars := chars.push c
    i := i + 1
  return (String.fromUTF8! (ByteArray.mk chars), i)

/-- Splits a NUL-separated string list (e.g. `compatible = "arm,pl011\0arm,primecell\0"`). -/
def splitNulStrings (raw : ByteArray) : Array String := Id.run do
  let mut res : Array String := #[]
  let mut cur : Array UInt8 := #[]
  for i in [0:raw.size] do
    let c := raw.get! i
    if c == 0 then
      if cur.size > 0 then
        res := res.push (String.fromUTF8! (ByteArray.mk cur))
        cur := #[]
    else
      cur := cur.push c
  if cur.size > 0 then
    res := res.push (String.fromUTF8! (ByteArray.mk cur))
  return res

/-- Parses `(base, size)` pairs from a `reg` property:
    - 16-byte tuples for `#address-cells = <2>, #size-cells = <2>` (QEMU `-M virt`),
    - 12-byte tuples for `#address-cells = <2>, #size-cells = <1>` (Tensor G4 `zumapro`). -/
def parseReg64Pairs (raw : ByteArray) : Array (UInt64 × UInt64) := Id.run do
  let mut out : Array (UInt64 × UInt64) := #[]
  if raw.size > 0 && raw.size % 16 == 0 then
    let n := raw.size / 16
    for i in [0:n] do
      let base := readBe64 raw (i * 16)
      let size := readBe64 raw (i * 16 + 8)
      out := out.push (base, size)
  else if raw.size > 0 && raw.size % 12 == 0 then
    let n := raw.size / 12
    for i in [0:n] do
      let base := readBe64 raw (i * 12)
      let size := (readBe32 raw (i * 12 + 8)).toUInt64
      out := out.push (base, size)
  return out

structure FdtHeader where
  totalsize : Nat
  offDtStruct : Nat
  offDtStrings : Nat
  version : Nat
  sizeDtStrings : Nat
  sizeDtStruct : Nat
  deriving BEq, Repr, Inhabited

/-- Validates the 40-byte FDT header. Fails closed on short blobs, wrong magic, or OOB sections. -/
def parseHeader (b : ByteArray) : Except String FdtHeader :=
  if b.size < 40 then .error "FDT shorter than 40-byte header"
  else if readBe32 b 0 != fdtMagic then .error "FDT bad magic"
  else
    let totalsize := (readBe32 b 4).toNat
    let offStruct := (readBe32 b 8).toNat
    let offStrings := (readBe32 b 12).toNat
    let version := (readBe32 b 20).toNat
    let sizeStrings := (readBe32 b 32).toNat
    let sizeStruct := (readBe32 b 36).toNat
    if totalsize < 40 || totalsize > b.size then .error "FDT totalsize out of bounds"
    else if version < 16 then .error "FDT unsupported version"
    else if offStruct + sizeStruct > totalsize then .error "FDT struct block out of bounds"
    else if offStrings + sizeStrings > totalsize then .error "FDT strings block out of bounds"
    else if offStruct % 4 != 0 then .error "FDT unaligned struct offset"
    else .ok {
      totalsize, offDtStruct := offStruct, offDtStrings := offStrings,
      version, sizeDtStrings := sizeStrings, sizeDtStruct := sizeStruct
    }

structure FdtNode where
  name : String
  compatibles : Array String := #[]
  regs : Array (UInt64 × UInt64) := #[]
  deriving BEq, Repr, Inhabited

structure ParsedFdt where
  bootargs : String := ""
  memoryRanges : Array (UInt64 × UInt64) := #[]
  nodes : Array FdtNode := #[]
  deriving BEq, Repr, Inhabited

private def parseStruct (b : ByteArray) (hdr : FdtHeader) (maxSteps : Nat) : Except String ParsedFdt := do
  let structEnd := hdr.offDtStruct + hdr.sizeDtStruct
  let stringsEnd := hdr.offDtStrings + hdr.sizeDtStrings
  let mut pos := hdr.offDtStruct
  let mut stack : List FdtNode := []
  let mut finished : Array FdtNode := #[]
  let mut bootargs := ""
  let mut memRanges : Array (UInt64 × UInt64) := #[]
  let mut steps := 0
  let mut done := false
  while steps < maxSteps && !done && pos + 4 ≤ structEnd do
    steps := steps + 1
    let tok := readBe32 b pos
    pos := pos + 4
    if tok == fdtBeginNode then
      let (nm, afterNul) := readCStr b pos 128
      pos := align4 afterNul
      stack := { name := nm } :: stack
    else if tok == fdtEndNode then
      match stack with
      | [] => throw "FDT unmatched FDT_END_NODE"
      | cur :: rest =>
        if cur.name.startsWith "memory" then
          memRanges := memRanges ++ cur.regs
        if cur.compatibles.size > 0 || cur.regs.size > 0 then
          finished := finished.push cur
        stack := rest
    else if tok == fdtProp then
      if pos + 8 > structEnd then throw "FDT truncated FDT_PROP"
      let plen := (readBe32 b pos).toNat
      let nameoff := (readBe32 b (pos + 4)).toNat
      pos := pos + 8
      if pos + plen > structEnd then throw "FDT prop value out of bounds"
      if hdr.offDtStrings + nameoff ≥ stringsEnd then throw "FDT prop name offset out of bounds"
      let (pname, _) := readCStr b (hdr.offDtStrings + nameoff) 128
      let pval := b.extract pos (pos + plen)
      pos := align4 (pos + plen)
      match stack with
      | cur :: rest =>
        if cur.name == "chosen" && pname == "bootargs" then
          let (s, _) := readCStr pval 0 1024
          bootargs := s
        let cur' :=
          if pname == "compatible" then { cur with compatibles := splitNulStrings pval }
          else if pname == "reg" then { cur with regs := parseReg64Pairs pval }
          else cur
        stack := cur' :: rest
      | [] => pure ()
    else if tok == fdtNop then
      pure ()
    else if tok == fdtEnd then
      done := true
    else
      throw s!"FDT unknown token {tok}"
  if !done then throw "FDT missing FDT_END or step limit exceeded"
  return { bootargs, memoryRanges := memRanges, nodes := finished }

/-- Parses an entire Flattened Device Tree with bounded fuel (`maxSteps`) so termination is total. -/
def parse (b : ByteArray) (maxSteps : Nat := 16384) : Except String ParsedFdt :=
  if maxSteps == 0 then .error "FDT step limit is zero"
  else match parseHeader b with
  | .error e => .error e
  | .ok hdr => parseStruct b hdr maxSteps

/-- Helper to locate all device nodes whose `compatible` list contains `needle`. -/
def ParsedFdt.findCompatible (fdt : ParsedFdt) (needle : String) : Array FdtNode :=
  fdt.nodes.filter fun n => n.compatibles.any (· == needle)

end Kernel.Fdt
