import Tricorder.Network
import Tricorder.Qr.Encode
import Tricorder.Ui.Font
import Tricorder.Ui.Frame

/-! # Unified LCARS Layout, Rendering, and Touch Hit-Testing

Every interactive button is represented once as a `DrawCmd.button`, so its rendered bounding box and
its touch hit-test rectangle are identical by construction (`Tricorder/Proofs/LayoutProofs.lean`). -/

namespace Tricorder.Ui

structure Rect where
  x : Nat
  y : Nat
  w : Nat
  h : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

namespace Rect

def contains (r : Rect) (px py : Nat) : Bool :=
  r.x ≤ px && px < r.x + r.w && r.y ≤ py && py < r.y + r.h

def disjoint (a b : Rect) : Bool :=
  a.x + a.w ≤ b.x || b.x + b.w ≤ a.x || a.y + a.h ≤ b.y || b.y + b.h ≤ a.y

end Rect

/-- All interactive LCARS buttons across every Tricorder screen. -/
inductive ButtonId where
  | pinDigit (d : Nat)
  | pinBackspace
  | pinSubmit
  | setupGenerate
  | setupRestore
  | setupPrevPage
  | setupNextPage
  | setupToPin
  | restoreLetter (c : Char)
  | restoreBackspace
  | restoreClear
  | restorePickWord (word : String)
  | restorePopWord
  | restoreSubmit
  | navHome
  | navInbox
  | navKeys
  | navDiag
  | lockNow
  | keysTab (tab : Nat)
  | exportKeys
  | scanInbox
  | openInboxItem (idx : Nat)
  | registerWallet
  | abortReview
  | armSign
  | confirmSign
  | runSelfTest
  | runBigTest
  | drawEntropy
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Declarative LCARS drawing command. -/
inductive DrawCmd where
  | rect (r : Rect) (color : Color)
  | pill (r : Rect) (color : Color) (radius : Nat)
  | elbowTop (x y railW barH outerR innerR totalW : Nat) (color bg : Color)
  | elbowBottom (x y railW barH outerR innerR totalW : Nat) (color bg : Color)
  | text (x y : Nat) (s : String) (scale : Nat) (color : Color)
  | textCentered (r : Rect) (s : String) (scale : Nat) (color : Color)
  | qr (r : Rect) (code : Qr.QrCode)
  | button (id : ButtonId) (r : Rect) (label : String) (bg fg : Color) (scale : Nat) (radius : Nat := 18)

/-- Extracts all `(ButtonId, Rect)` interactive hit targets in draw order. -/
def buttonsOf : List DrawCmd → List (ButtonId × Rect)
  | [] => []
  | .button id r _ _ _ _ _ :: rest => (id, r) :: buttonsOf rest
  | _ :: rest => buttonsOf rest

/-- Touch hit-test directly over the declarative command list. -/
def hitTest : List DrawCmd → Nat → Nat → Option ButtonId
  | [], _, _ => none
  | .button id r _ _ _ _ _ :: rest, px, py =>
    if r.contains px py then some id else hitTest rest px py
  | _ :: rest, px, py => hitTest rest px py

/-- Checks whether every pair of buttons in `cmds` has disjoint bounding rectangles. -/
def buttonsDisjoint (cmds : List DrawCmd) : Bool :=
  let bs := (buttonsOf cmds).toArray
  (List.range bs.size).all fun i =>
    (List.range i).all fun j => Rect.disjoint bs[i]!.2 bs[j]!.2

/-- Returns the `(ButtonId, Rect)` targeted by physical-button focus index `focusIdx` (wrapped mod button count). -/
def focusedTarget? (cmds : List DrawCmd) (focusIdx : Nat) : Option (ButtonId × Rect) :=
  let bs := buttonsOf cmds
  match bs with
  | [] => none
  | _ => bs[focusIdx % bs.length]?

def focusedButton? (cmds : List DrawCmd) (focusIdx : Nat) : Option ButtonId :=
  (focusedTarget? cmds focusIdx).map (·.1)

/-- Appends a high-contrast LCARS focus border around the currently focused button (for Volume/Power navigation). -/
def withFocusRing (cmds : List DrawCmd) (focusIdx : Nat) (ringColor : Color) : List DrawCmd :=
  match focusedTarget? cmds focusIdx with
  | none => cmds
  | some (_, r) =>
    let t := 4
    let pad := 3
    let x0 := if r.x ≥ pad then r.x - pad else 0
    let y0 := if r.y ≥ pad then r.y - pad else 0
    let w0 := r.w + 2 * pad
    let h0 := r.h + 2 * pad
    cmds ++ [
      .rect { x := x0, y := y0, w := w0, h := t } ringColor,
      .rect { x := x0, y := y0 + h0 - t, w := w0, h := t } ringColor,
      .rect { x := x0, y := y0, w := t, h := h0 } ringColor,
      .rect { x := x0 + w0 - t, y := y0, w := t, h := h0 } ringColor
    ]

/-- Renders a declarative LCARS command list into an RGBA_8888 `Frame`. -/
def renderCmds (width height : Nat) (bg : Color) (cmds : List DrawCmd) : Frame := Id.run do
  let mut f := Frame.blank width height bg
  for cmd in cmds do
    match cmd with
    | .rect r c => f := f.fillRect r.x r.y r.w r.h c
    | .pill r c rad => f := f.fillRoundedRect r.x r.y r.w r.h rad c
    | .elbowTop x y rw bh or' ir tw c bg' => f := f.drawLcarsElbowTop x y rw bh or' ir tw c bg'
    | .elbowBottom x y rw bh or' ir tw c bg' => f := f.drawLcarsElbowBottom x y rw bh or' ir tw c bg'
    | .text x y s sc c => f := f.drawText x y s sc c
    | .textCentered r s sc c =>
      let tw := Font.textWidth s sc
      let th := Font.textHeight sc
      let tx := if r.w ≥ tw then r.x + (r.w - tw) / 2 else r.x
      let ty := if r.h ≥ th then r.y + (r.h - th) / 2 else r.y
      f := f.drawText tx ty s sc c
    | .qr r code => f := f.drawQr r.x r.y r.w r.h code
    | .button _ r label fill fg sc rad =>
      f := f.fillRoundedRect r.x r.y r.w r.h rad fill
      let tw := Font.textWidth label sc
      let th := Font.textHeight sc
      let tx := if r.w ≥ tw then r.x + (r.w - tw) / 2 else r.x
      let ty := if r.h ≥ th then r.y + (r.h - th) / 2 else r.y
      f := f.drawText tx ty label sc fg
  return f

end Tricorder.Ui
