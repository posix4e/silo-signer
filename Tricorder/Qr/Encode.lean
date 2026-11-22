/-! # Pure-Lean ISO/IEC 18004 QR Code Encoder (Versions 1..40, EC Level L, Byte Mode)

Renders arbitrary UTF-8 / ASCII payloads up to 2,953 bytes directly to a `QrCode` bit-matrix for
zero-dependency display on Tricorder's LCARS framebuffer. -/

namespace Tricorder.Qr

structure QrCode where
  version : Nat
  size : Nat
  /-- Row-major `size * size` modules: `true` = dark, `false` = light. -/
  modules : Array Bool
  deriving BEq, Repr, Inhabited

def QrCode.get (qr : QrCode) (x y : Nat) : Bool :=
  if x < qr.size && y < qr.size then qr.modules[y * qr.size + x]! else false

/-- ISO 18004 EC Level L codewords per block for versions 1..40 (index 0 unused). -/
private def eccPerBlockL : Array Nat := #[
  0,  7, 10, 15, 20, 26, 18, 20, 24, 30, 18,
     20, 24, 26, 30, 22, 24, 28, 30, 28, 28,
     28, 28, 30, 30, 26, 28, 30, 30, 30, 30,
     30, 30, 30, 30, 30, 30, 30, 30, 30, 30]

/-- ISO 18004 EC Level L block counts for versions 1..40 (index 0 unused). -/
private def numBlocksL : Array Nat := #[
  0,  1,  1,  1,  1,  1,  2,  2,  2,  2,  4,
      4,  4,  4,  4,  6,  6,  6,  6,  7,  8,
      8,  9,  9, 10, 12, 12, 12, 13, 14, 15,
     16, 17, 18, 19, 19, 20, 21, 22, 24, 25]

private def rawDataModules (ver : Nat) : Nat :=
  let total := (16 * ver + 128) * ver + 64
  if ver < 2 then total
  else
    let numAlign := ver / 7 + 2
    let subAlign := (25 * numAlign - 10) * numAlign - 55
    let subVer := if ver ≥ 7 then 36 else 0
    total - subAlign - subVer

private def dataCodewordsL (ver : Nat) : Nat :=
  rawDataModules ver / 8 - eccPerBlockL[ver]! * numBlocksL[ver]!

private def alignmentPositions (ver : Nat) : Array Nat := Id.run do
  if ver == 1 then return #[]
  let numAlign := ver / 7 + 2
  let step := if ver == 32 then 26 else ((ver * 4 + numAlign * 2 + 1) / (numAlign * 2 - 2)) * 2
  let mut out := Array.replicate numAlign 6
  let mut pos := ver * 4 + 10
  for idx in [0:numAlign - 1] do
    let i := numAlign - 1 - idx
    out := out.set! i pos
    pos := pos - step
  return out

private def gfMul (x y : UInt8) : UInt8 := Id.run do
  let mut z : UInt16 := 0
  let mut a := x.toUInt16
  let b := y.toUInt16
  for i in [0:8] do
    let bit := (b >>> (7 - i).toUInt16) &&& 1
    z := (z <<< 1) ^^^ (if (z >>> 7) != 0 then 0x11d else 0)
    if bit != 0 then z := z ^^^ a
  return z.toUInt8

private def rsDivisor (degree : Nat) : Array UInt8 := Id.run do
  let mut r := Array.replicate degree (0 : UInt8)
  r := r.set! (degree - 1) 1
  let mut root : UInt8 := 1
  for _ in [0:degree] do
    for j in [0:degree] do
      let next := if j + 1 < degree then r[j + 1]! else 0
      r := r.set! j (gfMul r[j]! root ^^^ next)
    root := gfMul root 2
  return r

private def rsRemainder (data : ByteArray) (divisor : Array UInt8) : Array UInt8 := Id.run do
  let deg := divisor.size
  let mut rem := Array.replicate deg (0 : UInt8)
  for b in data.toList do
    let factor := b ^^^ rem[0]!
    for j in [0:deg] do
      let shifted := if j + 1 < deg then rem[j + 1]! else 0
      rem := rem.set! j (shifted ^^^ gfMul divisor[j]! factor)
  return rem

private def appendBits (bits : Array Bool) (val len : Nat) : Array Bool := Id.run do
  let mut out := bits
  for i in [0:len] do
    out := out.push (((val >>> (len - 1 - i)) &&& 1) == 1)
  return out

private def chooseVersion (byteLen : Nat) : Option Nat := Id.run do
  for v in [1:41] do
    let headerBits := 4 + (if v ≤ 9 then 8 else 16)
    let capBits := dataCodewordsL v * 8
    if headerBits + byteLen * 8 ≤ capBits then return some v
  return none

private def encodeDataAndEcc (ver : Nat) (payload : ByteArray) : ByteArray := Id.run do
  let capBytes := dataCodewordsL ver
  let capBits := capBytes * 8
  let mut bits : Array Bool := #[]
  bits := appendBits bits 4 4 -- Byte mode
  bits := appendBits bits payload.size (if ver ≤ 9 then 8 else 16)
  for b in payload.toList do
    bits := appendBits bits b.toNat 8
  let termLen := min 4 (capBits - bits.size)
  bits := appendBits bits 0 termLen
  while bits.size % 8 != 0 do bits := bits.push false
  let mut data := ByteArray.emptyWithCapacity capBytes
  for i in [0:bits.size / 8] do
    let mut byte : UInt8 := 0
    for j in [0:8] do
      byte := (byte <<< 1) ||| (if bits[i * 8 + j]! then 1 else 0)
    data := data.push byte
  let mut padToggle := true
  while data.size < capBytes do
    data := data.push (if padToggle then 0xEC else 0x11)
    padToggle := !padToggle
  -- Split into blocks, compute RS ECC, and interleave.
  let rawCw := rawDataModules ver / 8
  let nb := numBlocksL[ver]!
  let eccLen := eccPerBlockL[ver]!
  let numShort := nb - rawCw % nb
  let shortDataLen := rawCw / nb - eccLen
  let divisor := rsDivisor eccLen
  let mut blocks : Array (ByteArray × Array UInt8) := #[]
  let mut off := 0
  for i in [0:nb] do
    let dlen := shortDataLen + (if i < numShort then 0 else 1)
    let blk := data.extract off (off + dlen)
    off := off + dlen
    blocks := blocks.push (blk, rsRemainder blk divisor)
  let mut out := ByteArray.emptyWithCapacity rawCw
  let maxData := shortDataLen + (if numShort < nb then 1 else 0)
  for j in [0:maxData] do
    for (blk, _) in blocks do
      if j < blk.size then out := out.push blk[j]!
  for j in [0:eccLen] do
    for (_, ecc) in blocks do
      out := out.push ecc[j]!
  return out

private def setFunc (sz : Nat) (mods isFunc : Array Bool) (x y : Nat) (dark : Bool) : Array Bool × Array Bool :=
  if x < sz && y < sz then
    let idx := y * sz + x
    (mods.set! idx dark, isFunc.set! idx true)
  else (mods, isFunc)

private def drawFinder (sz : Nat) (mods isFunc : Array Bool) (cx cy : Int) : Array Bool × Array Bool := Id.run do
  let mut m := mods; let mut f := isFunc
  for r in [0:9] do
    for c in [0:9] do
      let dx : Int := (c : Int) - 4
      let dy : Int := (r : Int) - 4
      let x := cx + dx; let y := cy + dy
      if x ≥ 0 && x < sz && y ≥ 0 && y < sz then
        let dist := max dx.natAbs dy.natAbs
        let dark := dist != 2 && dist != 4
        (m, f) := setFunc sz m f x.toNat y.toNat dark
  return (m, f)

private def drawAlignment (sz : Nat) (mods isFunc : Array Bool) (cx cy : Nat) : Array Bool × Array Bool := Id.run do
  let mut m := mods; let mut f := isFunc
  for dy in [0:5] do
    for dx in [0:5] do
      let ddx := if dx ≥ 2 then dx - 2 else 2 - dx
      let ddy := if dy ≥ 2 then dy - 2 else 2 - dy
      let dark := max ddx ddy != 1
      (m, f) := setFunc sz m f (cx + dx - 2) (cy + dy - 2) dark
  return (m, f)

private def drawFormatBits (sz : Nat) (mods isFunc : Array Bool) (mask : Nat) : Array Bool × Array Bool := Id.run do
  -- EC Level L format indicator = 01 (1).
  let data : UInt32 := ((1 : UInt32) <<< 3) ||| mask.toUInt32
  let mut rem : UInt32 := data
  for _ in [0:10] do
    rem := (rem <<< 1) ^^^ ((rem >>> 9) * 0x537)
  let bits : UInt32 := ((data <<< 10) ||| rem) ^^^ 0x5412
  let bit (i : Nat) : Bool := ((bits >>> i.toUInt32) &&& 1) == 1
  let mut m := mods; let mut f := isFunc
  for i in [0:6] do (m, f) := setFunc sz m f 8 i (bit i)
  (m, f) := setFunc sz m f 8 7 (bit 6)
  (m, f) := setFunc sz m f 8 8 (bit 7)
  (m, f) := setFunc sz m f 7 8 (bit 8)
  for i in [9:15] do (m, f) := setFunc sz m f (14 - i) 8 (bit i)
  for i in [0:8] do (m, f) := setFunc sz m f (sz - 1 - i) 8 (bit i)
  for i in [8:15] do (m, f) := setFunc sz m f 8 (sz - 15 + i) (bit i)
  (m, f) := setFunc sz m f 8 (sz - 8) true -- dark module
  return (m, f)

private def drawVersionBits (ver sz : Nat) (mods isFunc : Array Bool) : Array Bool × Array Bool := Id.run do
  if ver < 7 then return (mods, isFunc)
  let v32 : UInt32 := ver.toUInt32
  let mut rem : UInt32 := v32
  for _ in [0:12] do
    rem := (rem <<< 1) ^^^ ((rem >>> 11) * 0x1F25)
  let bits : UInt32 := (v32 <<< 12) ||| rem
  let mut m := mods; let mut f := isFunc
  for i in [0:18] do
    let dark := ((bits >>> i.toUInt32) &&& 1) == 1
    let a := sz - 11 + i % 3
    let b := i / 3
    (m, f) := setFunc sz m f a b dark
    (m, f) := setFunc sz m f b a dark
  return (m, f)

private def maskCond (mask x y : Nat) : Bool :=
  match mask with
  | 0 => (x + y) % 2 == 0
  | 1 => y % 2 == 0
  | 2 => x % 3 == 0
  | 3 => (x + y) % 3 == 0
  | 4 => (x / 3 + y / 2) % 2 == 0
  | 5 => (x * y) % 2 + (x * y) % 3 == 0
  | 6 => ((x * y) % 2 + (x * y) % 3) % 2 == 0
  | _ => ((x + y) % 2 + (x * y) % 3) % 2 == 0

private def penaltyScore (sz : Nat) (mods : Array Bool) : Nat := Id.run do
  let at' (x y : Nat) : Bool := mods[y * sz + x]!
  let mut score := 0
  -- Rule 1: adjacent runs >= 5 (rows and cols)
  for y in [0:sz] do
    let mut runColor := at' 0 y
    let mut runLen := 1
    for x in [1:sz] do
      let c := at' x y
      if c == runColor then
        runLen := runLen + 1
        if runLen == 5 then score := score + 3
        else if runLen > 5 then score := score + 1
      else
        runColor := c; runLen := 1
  for x in [0:sz] do
    let mut runColor := at' x 0
    let mut runLen := 1
    for y in [1:sz] do
      let c := at' x y
      if c == runColor then
        runLen := runLen + 1
        if runLen == 5 then score := score + 3
        else if runLen > 5 then score := score + 1
      else
        runColor := c; runLen := 1
  -- Rule 2: 2x2 blocks
  for y in [0:sz - 1] do
    for x in [0:sz - 1] do
      let c := at' x y
      if c == at' (x + 1) y && c == at' x (y + 1) && c == at' (x + 1) (y + 1) then
        score := score + 3
  -- Rule 4: dark ratio balance
  let mut dark := 0
  for b in mods do if b then dark := dark + 1
  let total := sz * sz
  let pct := (dark * 100) / total
  let diff := if pct ≥ 50 then pct - 50 else 50 - pct
  score := score + (diff / 5) * 10
  return score

/-- Encodes `payload` into a QR Code (EC Level L, Byte Mode). Returns `none` if > 2953 bytes. -/
def encodeBytes (payload : ByteArray) : Option QrCode := Id.run do
  let some ver := chooseVersion payload.size | return none
  let sz := ver * 4 + 17
  let codewords := encodeDataAndEcc ver payload
  let mut mods := Array.replicate (sz * sz) false
  let mut isFunc := Array.replicate (sz * sz) false
  -- Timing patterns
  for i in [0:sz] do
    let dark := i % 2 == 0
    (mods, isFunc) := setFunc sz mods isFunc 6 i dark
    (mods, isFunc) := setFunc sz mods isFunc i 6 dark
  -- Finder patterns
  (mods, isFunc) := drawFinder sz mods isFunc 3 3
  (mods, isFunc) := drawFinder sz mods isFunc (sz - 4) 3
  (mods, isFunc) := drawFinder sz mods isFunc 3 (sz - 4)
  -- Alignment patterns
  let aligns := alignmentPositions ver
  let n := aligns.size
  for i in [0:n] do
    for j in [0:n] do
      let corner := (i == 0 && j == 0) || (i == 0 && j == n - 1) || (i == n - 1 && j == 0)
      if !corner then
        (mods, isFunc) := drawAlignment sz mods isFunc aligns[i]! aligns[j]!
  -- Reserve format & version bits
  (mods, isFunc) := drawFormatBits sz mods isFunc 0
  (mods, isFunc) := drawVersionBits ver sz mods isFunc
  -- Place codewords in zig-zag columns
  let mut bitIdx := 0
  let totalBits := codewords.size * 8
  let mut right : Int := sz - 1
  while right ≥ 1 do
    if right == 6 then right := 5
    for vert in [0:sz] do
      let up := ((right.toNat + 1) &&& 2) == 0
      let y := if up then sz - 1 - vert else vert
      for j in [0:2] do
        let x := (right - j).toNat
        if !isFunc[y * sz + x]! then
          let dark :=
            if bitIdx < totalBits then
              let b := codewords[bitIdx / 8]!
              ((b.toNat >>> (7 - (bitIdx % 8))) &&& 1) == 1
            else false
          mods := mods.set! (y * sz + x) dark
          bitIdx := bitIdx + 1
    right := right - 2
  -- Evaluate masks 0..7 and pick lowest penalty
  let mut bestScore := 1000000000
  let mut bestMods := mods
  for mask in [0:8] do
    let mut cand := mods
    for y in [0:sz] do
      for x in [0:sz] do
        let idx := y * sz + x
        if !isFunc[idx]! && maskCond mask x y then
          cand := cand.set! idx (!cand[idx]!)
    let (masked, _) := drawFormatBits sz cand isFunc mask
    let sc := penaltyScore sz masked
    if sc < bestScore then
      bestScore := sc
      bestMods := masked
  return some { version := ver, size := sz, modules := bestMods }

def encode (text : String) : Option QrCode :=
  encodeBytes text.toUTF8

end Tricorder.Qr
