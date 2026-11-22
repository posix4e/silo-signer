import Tricorder.Network
import Tricorder.Qr.Encode
import Tricorder.Ui.Font

/-! # Pure-Lean RGBA_8888 software framebuffer for LCARS rendering

Produces exact RGBA_8888 pixel buffers (`width * height * 4` bytes) that blit directly into
Blitted directly to QEMU `ramfb` or Pixel 9 DECON OLED framebuffer via `Kernel.Fb`, and exported
as P6 `.ppm` images in macOS headless tests. -/

namespace Tricorder.Ui

structure Frame where
  width : Nat
  height : Nat
  /-- RGBA_8888 bytes (`width * height * 4`). -/
  pixels : ByteArray

namespace Frame

def blank (width height : Nat) (bg : Color := Color.black) : Frame := Id.run do
  let n := width * height
  let r := (bg &&& 0xff).toUInt8
  let g := ((bg >>> 8) &&& 0xff).toUInt8
  let b := ((bg >>> 16) &&& 0xff).toUInt8
  let a := ((bg >>> 24) &&& 0xff).toUInt8
  if r == 0 && g == 0 && b == 0 && a == 255 then
    -- Fast OLED black fill: build one 1024-pixel chunk and replicate
    let mut row := ByteArray.emptyWithCapacity (width * 4)
    for _ in [0:width] do
      row := (((row.push 0).push 0).push 0).push 255
    let mut out := ByteArray.emptyWithCapacity (n * 4)
    for _ in [0:height] do out := out ++ row
    return { width, height, pixels := out }
  else
    let mut row := ByteArray.emptyWithCapacity (width * 4)
    for _ in [0:width] do
      row := (((row.push r).push g).push b).push a
    let mut out := ByteArray.emptyWithCapacity (n * 4)
    for _ in [0:height] do out := out ++ row
    return { width, height, pixels := out }

@[inline] private def putPixel (data : ByteArray) (w h x y : Nat) (r g b a : UInt8) : ByteArray :=
  if x < w && y < h then
    let off := (y * w + x) * 4
    if off + 3 < data.size then
      (((data.set! off r).set! (off + 1) g).set! (off + 2) b).set! (off + 3) a
    else data
  else data

def fillRect (f : Frame) (x y w h : Nat) (color : Color) : Frame := Id.run do
  let r := (color &&& 0xff).toUInt8
  let g := ((color >>> 8) &&& 0xff).toUInt8
  let b := ((color >>> 16) &&& 0xff).toUInt8
  let a := ((color >>> 24) &&& 0xff).toUInt8
  let x1 := min (x + w) f.width
  let y1 := min (y + h) f.height
  if x ≥ x1 || y ≥ y1 then return f
  let span := x1 - x
  let mut line := ByteArray.emptyWithCapacity (span * 4)
  for _ in [0:span] do
    line := (((line.push r).push g).push b).push a
  let mut px := f.pixels
  for py in [y:y1] do
    px := line.copySlice 0 px ((py * f.width + x) * 4) (span * 4)
  return { f with pixels := px }

/-- Rounded rectangle (LCARS pills & cards) using exact integer-circle corner masks. -/
def fillRoundedRect (f : Frame) (x y w h radius : Nat) (color : Color) : Frame := Id.run do
  if w == 0 || h == 0 then return f
  let rad := min radius (min (w / 2) (h / 2))
  if rad == 0 then return f.fillRect x y w h color
  -- Center body (fast copySlice)
  let mut out := f.fillRect x (y + rad) w (h - 2 * rad) color
  let r2 := rad * rad
  -- Top and bottom rounded bands row by row using fast horizontal spans
  for dy in [0:rad] do
    let d := rad - 1 - dy
    let mut dx := 0
    while dx < rad && (rad - 1 - dx) * (rad - 1 - dx) + d * d ≥ r2 do
      dx := dx + 1
    let spanW := w - 2 * dx
    if spanW > 0 then
      out := out.fillRect (x + dx) (y + dy) spanW 1 color
      out := out.fillRect (x + dx) (y + h - 1 - dy) spanW 1 color
  return out

/-- Top-left sweeping elbow: outer rounded corner + inner concave sweep. -/
def drawLcarsElbowTop (f : Frame) (x y railW barH outerR innerR totalW : Nat) (color bg : Color) : Frame := Id.run do
  let totalH := barH + innerR
  let mut out := f.fillRoundedRect x y totalW totalH outerR color
  -- Square off right end of top bar and bottom end of vertical rail
  out := out.fillRect (x + totalW - outerR) y outerR barH color
  out := out.fillRect x (y + totalH - outerR) railW outerR color
  -- Cut out inner right-bottom area with concave top-left arc
  let cutX := x + railW
  let cutY := y + barH
  let cutW := totalW - railW
  let cutH := innerR
  out := out.fillRect (cutX + innerR) cutY (cutW - innerR) cutH bg
  let r2 := innerR * innerR
  for dy in [0:innerR] do
    let d := innerR - 1 - dy
    let mut dx := 0
    while dx < innerR && (innerR - 1 - dx) * (innerR - 1 - dx) + d * d ≥ r2 do
      dx := dx + 1
    if dx < innerR then
      out := out.fillRect (cutX + dx) (cutY + dy) (innerR - dx) 1 bg
  return out

/-- Bottom-left sweeping elbow. -/
def drawLcarsElbowBottom (f : Frame) (x y railW barH outerR innerR totalW : Nat) (color bg : Color) : Frame := Id.run do
  let totalH := barH + innerR
  let mut out := f.fillRoundedRect x y totalW totalH outerR color
  out := out.fillRect (x + totalW - outerR) (y + innerR) outerR barH color
  out := out.fillRect x y railW outerR color
  let cutX := x + railW
  let cutY := y
  let cutW := totalW - railW
  let cutH := innerR
  out := out.fillRect (cutX + innerR) cutY (cutW - innerR) cutH bg
  let r2 := innerR * innerR
  for dy in [0:innerR] do
    let d := dy
    let mut dx := 0
    while dx < innerR && (innerR - 1 - dx) * (innerR - 1 - dx) + d * d ≥ r2 do
      dx := dx + 1
    if dx < innerR then
      out := out.fillRect (cutX + dx) (cutY + dy) (innerR - dx) 1 bg
  return out

def drawText (f : Frame) (x y : Nat) (text : String) (scale : Nat) (color : Color) : Frame := Id.run do
  if scale == 0 || text.isEmpty then return f
  let r := (color &&& 0xff).toUInt8
  let g := ((color >>> 8) &&& 0xff).toUInt8
  let b := ((color >>> 16) &&& 0xff).toUInt8
  let a := ((color >>> 24) &&& 0xff).toUInt8
  let mut px := f.pixels
  let mut cx := x
  for ch in text.toList do
    let rows := Font.glyph ch
    for rowIdx in [0:7] do
      let bits := rows[rowIdx]!
      if bits != 0 then
        for col in [0:5] do
          if ((bits >>> (4 - col).toUInt8) &&& 1) == 1 then
            let gx := cx + col * scale
            let gy := y + rowIdx * scale
            for sy in [0:scale] do
              for sx in [0:scale] do
                px := putPixel px f.width f.height (gx + sx) (gy + sy) r g b a
    cx := cx + 6 * scale
  return { f with pixels := px }

/-- Draws a QR code centered inside `(x, y, w, h)` with a crisp white 4-module quiet zone. -/
def drawQr (f : Frame) (x y w h : Nat) (qr : Qr.QrCode) : Frame := Id.run do
  let totalMods := qr.size + 8 -- 4-module quiet zone on each side
  let side := min w h
  let cell := max 1 (side / totalMods)
  let boxPx := cell * totalMods
  let ox := x + (w - min w boxPx) / 2
  let oy := y + (h - min h boxPx) / 2
  let mut out := f.fillRect ox oy boxPx boxPx Color.white
  for my in [0:qr.size] do
    for mx in [0:qr.size] do
      if qr.get mx my then
        out := out.fillRect (ox + (mx + 4) * cell) (oy + (my + 4) * cell) cell cell Color.black
  return out

/-- Exports the frame as binary PPM (`P6`) for macOS headless visual verification. -/
def toPpm (f : Frame) : ByteArray := Id.run do
  let header := s!"P6\n{f.width} {f.height}\n255\n".toUTF8
  let mut rgb := ByteArray.emptyWithCapacity (header.size + f.width * f.height * 3)
  rgb := rgb ++ header
  let n := f.width * f.height
  for i in [0:n] do
    let off := i * 4
    rgb := ((rgb.push f.pixels[off]!).push f.pixels[off + 1]!).push f.pixels[off + 2]!
  return rgb

end Frame

end Tricorder.Ui
