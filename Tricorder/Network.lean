import Winnow.Tx

/-! # Network configuration and LCARS palettes

One Bitcoin network per build (`regtest`, `signet`, or `mainnet`), each with a distinct Star Trek
LCARS color scheme so networks are visually unmistakable on the bare-metal OLED display. -/

namespace Tricorder

open Winnow.Tx (BitcoinNetwork)

/-- Packed `RGBA_8888` pixel (little-endian: R in low byte, converted on blit for target scanout format). -/
abbrev Color := UInt32

namespace Color

@[inline] def rgba (r g b : UInt8) (a : UInt8 := 255) : Color :=
  r.toUInt32 ||| (g.toUInt32 <<< 8) ||| (b.toUInt32 <<< 16) ||| (a.toUInt32 <<< 24)

@[inline] def rgb (r g b : UInt8) : Color := rgba r g b 255

def black : Color := rgb 0 0 0
def white : Color := rgb 245 245 250
def panelBg : Color := rgb 16 18 24
def dimText : Color := rgb 150 155 170
def redAlert : Color := rgb 238 68 68
def greenOk : Color := rgb 80 210 130

end Color

/-- Star Trek LCARS palette for a network build. -/
structure Palette where
  /-- Primary rail & elbow accent. -/
  primary : Color
  /-- Secondary bar & action pill accent. -/
  secondary : Color
  /-- Tertiary accent for data cards & labels. -/
  accent : Color
  /-- Highlight color for titles and active controls. -/
  highlight : Color
  /-- Danger / abort / red-alert accent. -/
  alert : Color
  /-- Positive / verified accent. -/
  ok : Color
  /-- OLED background. -/
  bg : Color
  /-- Card surface. -/
  surface : Color
  /-- Main foreground text on dark background. -/
  fg : Color
  /-- Text drawn on bright LCARS pills. -/
  pillFg : Color
  deriving BEq, Repr, Inhabited

/-- Network identity compiled into a Tricorder build. -/
inductive Network where
  | regtest
  | signet
  | mainnet
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Network

def toBitcoin : Network → BitcoinNetwork
  | .regtest => .regtest
  | .signet => .signet
  | .mainnet => .mainnet

def tagByte : Network → UInt8
  | .regtest => 1
  | .signet => 2
  | .mainnet => 3

def name : Network → String
  | .regtest => "regtest"
  | .signet => "signet"
  | .mainnet => "mainnet"

def upperName : Network → String
  | .regtest => "REGTEST"
  | .signet => "SIGNET"
  | .mainnet => "MAINNET"

def parse? : String → Option Network
  | "regtest" => some .regtest
  | "signet" => some .signet
  | "mainnet" => some .mainnet
  | _ => none

/-- Distinct LCARS color schemes per network:
- Mainnet: Classic TNG Command Gold / Peach / Lavender
- Signet: Science Division Cyan / Periwinkle / Ice Blue
- Regtest: Tactical Operations Amber-Rust / Coral / Ochre -/
def palette : Network → Palette
  | .mainnet =>
    { primary := Color.rgb 255 153 0     -- TNG Gold #FF9900
      secondary := Color.rgb 204 153 204 -- TNG Lavender #CC99CC
      accent := Color.rgb 255 204 153    -- TNG Peach #FFCC99
      highlight := Color.rgb 255 215 120
      alert := Color.rgb 221 68 68       -- Red Alert #DD4444
      ok := Color.rgb 102 221 153
      bg := Color.black
      surface := Color.rgb 18 16 14
      fg := Color.rgb 255 224 178
      pillFg := Color.black }
  | .signet =>
    { primary := Color.rgb 102 204 255   -- Science Cyan #66CCFF
      secondary := Color.rgb 153 153 255 -- Periwinkle #9999FF
      accent := Color.rgb 153 230 230    -- Ice Teal #99E6E6
      highlight := Color.rgb 204 240 255
      alert := Color.rgb 255 102 102
      ok := Color.rgb 102 238 170
      bg := Color.black
      surface := Color.rgb 12 18 24
      fg := Color.rgb 210 238 255
      pillFg := Color.black }
  | .regtest =>
    { primary := Color.rgb 255 102 51    -- Tactical Rust #FF6633
      secondary := Color.rgb 255 170 68  -- Ops Amber #FFAA44
      accent := Color.rgb 238 153 136    -- Coral #EE9988
      highlight := Color.rgb 255 210 150
      alert := Color.rgb 255 51 68
      ok := Color.rgb 120 225 140
      bg := Color.black
      surface := Color.rgb 24 14 12
      fg := Color.rgb 255 218 196
      pillFg := Color.black }

end Network

end Tricorder
