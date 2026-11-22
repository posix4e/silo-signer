import Tricorder.Network
import Tricorder.Qr.Encode
import Tricorder.Ui.Font
import Tricorder.Ui.Layout
import Tricorder.Ui.State

/-! # Star Trek LCARS View Renderer

Builds a pure `List DrawCmd` for every Tricorder screen at logical resolution `w × h` (default `540 × 1200`
for Pixel 9 Pro XL's 9:20 OLED display), with explicit top/bottom safe insets for the camera cutout and
gesture bar. Every interactive button is emitted via `DrawCmd.button`, guaranteeing rendered rects and
hitboxes match identically. -/

namespace Tricorder.Ui.View

open Tricorder.Signer

/-- Formats satoshis cleanly as `"123,456 SAT (0.00123456 BTC)"` or compact `"250,000 SAT"`. -/
def formatSats (sats : Nat) : String :=
  let s := toString sats
  let cs := s.toList.reverse
  let rec group (i : Nat) : List Char → List Char
    | [] => []
    | c :: rest =>
      if i > 0 && i % 3 == 0 then ',' :: c :: group (i + 1) rest
      else c :: group (i + 1) rest
  String.ofList (group 0 cs).reverse ++ " SAT"

private def truncStr (s : String) (maxLen : Nat) : String :=
  if s.length ≤ maxLen then s else (s.take (maxLen - 3)).toString ++ "..."

private def wrapLines (s : String) (cols : Nat) (maxLines : Nat) : List String := Id.run do
  if cols == 0 then return []
  let cs := s.toList
  let mut out : List String := []
  let mut rem := cs
  let mut k := 0
  while !rem.isEmpty && k < maxLines do
    let chunk := rem.take cols
    rem := rem.drop cols
    out := out ++ [String.ofList chunk]
    k := k + 1
  return out

/-- Draws the LCARS chrome frame: top elbow, header title bar, segmented left command rail, status bar,
and bottom elbow. Returns the usable content rectangle `(cx, cy, cw, ch)`. -/
private def lcarsChrome (w h topInset bottomInset : Nat) (pal : Palette) (net : Network)
    (title : String) (statusMsg : String) (isErr : Bool) (unlocked : Bool) :
    List DrawCmd × Rect :=
  let pad := 10
  let railW := 74
  let barH := 42
  let elbowY := topInset + 8
  let footBarH := 32
  let footY := h - bottomInset - footBarH - 22
  let contentX := pad + railW + 14
  let contentW := w - contentX - pad
  let headerRightX := contentX
  let topBarX := pad
  let topBarTotalW := w - 2 * pad
  let statusY := elbowY + barH + 10
  let statusH := 34
  let bodyY := statusY + statusH + 12
  let bodyH := if footY > bodyY + 12 then footY - bodyY - 12 else 200
  let statusBg := if isErr then pal.alert else pal.surface
  let statusFg := if isErr then Color.white else pal.accent
  let railTop := elbowY + barH + 34
  let railAvail := if footY > railTop + 16 then footY - railTop - 16 else 120
  let seg1 := railAvail / 3
  let seg2 := railAvail / 3
  let seg3 := railAvail - seg1 - seg2 - 12
  let badgeColor := match net with
    | .mainnet => pal.alert
    | .signet => pal.primary
    | .regtest => pal.secondary
  let chrome : List DrawCmd := [
    -- Top LCARS elbow
    .elbowTop topBarX elbowY railW barH 34 22 topBarTotalW pal.primary pal.bg,
    -- Cutout inside top bar for title & network badge
    .rect { x := headerRightX + 2, y := elbowY, w := contentW - 102, h := barH } pal.bg,
    .text (headerRightX + 10) (elbowY + 10) (truncStr title 15) 3 pal.highlight,
    -- Network pill on top right
    .pill { x := w - pad - 96, y := elbowY + 4, w := 96, h := barH - 8 } badgeColor 14,
    .textCentered { x := w - pad - 96, y := elbowY + 4, w := 96, h := barH - 8 } net.upperName 2 pal.pillFg,
    -- Left rail LCARS telemetry blocks
    .rect { x := pad, y := railTop, w := railW, h := seg1 } pal.secondary,
    .textCentered { x := pad, y := railTop + 8, w := railW, h := 22 } "47-01" 2 pal.pillFg,
    .textCentered { x := pad, y := railTop + 32, w := railW, h := 22 } (if unlocked then "OPEN" else "LOCK") 2 pal.pillFg,
    .rect { x := pad, y := railTop + seg1 + 6, w := railW, h := seg2 } pal.accent,
    .textCentered { x := pad, y := railTop + seg1 + 14, w := railW, h := 22 } "SECP" 2 pal.pillFg,
    .textCentered { x := pad, y := railTop + seg1 + 38, w := railW, h := 22 } "CT-OK" 2 pal.pillFg,
    .rect { x := pad, y := railTop + seg1 + seg2 + 12, w := railW, h := seg3 } pal.primary,
    .textCentered { x := pad, y := railTop + seg1 + seg2 + 20, w := railW, h := 22 } "0-OS" 2 pal.pillFg,
    -- Status strip
    .pill { x := contentX, y := statusY, w := contentW, h := statusH } statusBg 12,
    .textCentered { x := contentX + 6, y := statusY, w := contentW - 12, h := statusH } (truncStr statusMsg 32) 2 statusFg,
    -- Bottom LCARS elbow
    .elbowBottom pad footY railW footBarH 28 18 topBarTotalW pal.secondary pal.bg,
    .rect { x := headerRightX + 2, y := footY + 18, w := 310, h := footBarH } pal.bg,
    .text (headerRightX + 12) (footY + 26) "SILO TRICORDER // LEAN 4" 2 Color.dimText
  ]
  (chrome, { x := contentX, y := bodyY, w := contentW, h := bodyH })

/-- LCARS 3×4 numeric PIN keypad (digits 1-9, DEL, 0, OK). -/
private def pinPadCmds (cx cy cw : Nat) (pal : Palette) (pinLen : Nat) (submitLabel : String) : List DrawCmd := Id.run do
  let mut cmds : List DrawCmd := []
  -- PIN dots display box
  let boxH := 64
  cmds := cmds ++ [
    .pill { x := cx, y := cy, w := cw, h := boxH } pal.surface 16,
    .textCentered { x := cx, y := cy, w := cw, h := boxH }
      (if pinLen == 0 then "------" else String.ofList (List.replicate pinLen '*')) 4 pal.highlight
  ]
  let gap := 12
  let btnW := (cw - 2 * gap) / 3
  let btnH := 82
  let startY := cy + boxH + 22
  let rows : List (List (String × ButtonId × Color)) := [
    [("1", .pinDigit 1, pal.accent), ("2", .pinDigit 2, pal.accent), ("3", .pinDigit 3, pal.accent)],
    [("4", .pinDigit 4, pal.accent), ("5", .pinDigit 5, pal.accent), ("6", .pinDigit 6, pal.accent)],
    [("7", .pinDigit 7, pal.accent), ("8", .pinDigit 8, pal.accent), ("9", .pinDigit 9, pal.accent)],
    [("DEL", .pinBackspace, pal.secondary), ("0", .pinDigit 0, pal.accent), (submitLabel, .pinSubmit, pal.primary)]
  ]
  let mut ry := startY
  for row in rows do
    let mut rx := cx
    for (lbl, id, col) in row do
      cmds := cmds ++ [.button id { x := rx, y := ry, w := btnW, h := btnH } lbl col pal.pillFg 3 22]
      rx := rx + btnW + gap
    ry := ry + btnH + gap
  return cmds

/-- Builds the complete declarative LCARS `List DrawCmd` for the current model and viewport. -/
def view (m : Model) (w h : Nat := 540) (topInset : Nat := 64) (bottomInset : Nat := 44) : List DrawCmd :=
  let pal := m.network.palette
  let title := match m.screen with
    | .locked => "ACCESS LOCKED"
    | .setupChoice => "INIT KEY"
    | .setupWords _ p => s!"WORDS {p + 1}/2"
    | .setupRestore entered _ => s!"RESTORE {entered.size}/24"
    | .setupPin _ none _ => "SET PIN"
    | .setupPin _ (some _) _ => "CONFIRM PIN"
    | .home => "TRICORDER"
    | .keys _ => "PUBLIC KEYS"
    | .inbox _ => "AIR-GAP INBOX"
    | .reviewDescriptor .. => "VERIFY WALLET"
    | .reviewTx _ false => "REVIEW TX"
    | .reviewTx _ true => "ARMED TO SIGN"
    | .signed _ => "SIGNED"
    | .diagnostics .. => "DIAGNOSTICS"
  let (chrome, body) := lcarsChrome w h topInset bottomInset pal m.network title m.statusMsg m.isError m.secrets.isSome
  let cx := body.x; let cy := body.y; let cw := body.w; let ch := body.h
  let content : List DrawCmd := match m.screen with
  | .locked =>
    let remaining := Vault.maxFailedAttempts - min m.failedAttempts Vault.maxFailedAttempts
    [ .pill { x := cx, y := cy, w := cw, h := 68 } pal.surface 14,
      .text (cx + 14) (cy + 12) "AIR-GAPPED SILO SIGNER" 2 pal.primary,
      .text (cx + 14) (cy + 40) s!"ATTEMPTS REMAINING: {remaining} / {Vault.maxFailedAttempts}" 2
        (if remaining ≤ 3 then pal.alert else pal.fg) ] ++
    pinPadCmds cx (cy + 88) cw pal m.pinInput.length "OPEN"

  | .setupChoice =>
    [ .pill { x := cx, y := cy, w := cw, h := 148 } pal.surface 16,
      .text (cx + 16) (cy + 18) "STARFLEET SILO SIGNER" 3 pal.highlight,
      .text (cx + 16) (cy + 58) "ZERO JAVA // VERIFIED LEAN 4" 2 pal.accent,
      .text (cx + 16) (cy + 86) "SECPCT CONSTANT-TIME CURVE" 2 pal.fg,
      .text (cx + 16) (cy + 114) s!"NETWORK: {m.network.upperName} (AIR-GAPPED)" 2 pal.primary,
      .button .setupGenerate { x := cx, y := cy + 178, w := cw, h := 92 } "GENERATE NEW 24 WORDS" pal.primary pal.pillFg 3 24,
      .button .setupRestore { x := cx, y := cy + 292, w := cw, h := 92 } "RESTORE FROM 24 WORDS" pal.secondary pal.pillFg 3 24 ]

  | .setupWords words page => Id.run do
    let startIdx := if page == 0 then 0 else 12
    let mut cmds : List DrawCmd := [
      .text cx cy "WRITE ON PAPER - NEVER PHOTOGRAPH" 2 pal.alert
    ]
    let colW := (cw - 10) / 2
    let rowH := 56
    for row in [0:6] do
      for col in [0:2] do
        let idx := startIdx + row * 2 + col
        let word := words[idx]?.getD ""
        let bx := cx + col * (colW + 10)
        let by' := cy + 28 + row * (rowH + 8)
        cmds := cmds ++ [
          .pill { x := bx, y := by', w := colW, h := rowH } pal.surface 12,
          .text (bx + 10) (by' + 18) s!"{idx + 1}. {word.toUpper}" 2 pal.highlight
        ]
    let btnY := cy + ch - 82
    let halfW := (cw - 12) / 2
    if page == 0 then
      cmds := cmds ++ [
        .button .setupPrevPage { x := cx, y := btnY, w := halfW, h := 76 } "BACK" pal.secondary pal.pillFg 3 20,
        .button .setupNextPage { x := cx + halfW + 12, y := btnY, w := halfW, h := 76 } "WORDS 13-24" pal.primary pal.pillFg 3 20
      ]
    else
      cmds := cmds ++ [
        .button .setupPrevPage { x := cx, y := btnY, w := halfW, h := 76 } "WORDS 1-12" pal.secondary pal.pillFg 3 20,
        .button .setupToPin { x := cx + halfW + 12, y := btnY, w := halfW, h := 76 } "SET PIN" pal.ok pal.pillFg 3 20
      ]
    return cmds

  | .setupRestore entered pref => Id.run do
    let cands := Bip39Ascii.matchingPrefix pref 6
    let mut cmds : List DrawCmd := [
      .pill { x := cx, y := cy, w := cw, h := 58 } pal.surface 12,
      .text (cx + 12) (cy + 10) s!"WORD {min 24 (entered.size + 1)}/24: {pref.toUpper}_" 3 pal.highlight
    ]
    -- Matching BIP39 suggestion pills (up to 6, 2 columns × 3 rows)
    let sugY := cy + 70
    let halfW := (cw - 10) / 2
    for i in [0:cands.size] do
      let col := i % 2; let row := i / 2
      let wStr := cands[i]!
      cmds := cmds ++ [
        .button (.restorePickWord wStr)
          { x := cx + col * (halfW + 10), y := sugY + row * 54, w := halfW, h := 46 }
          wStr.toUpper pal.accent pal.pillFg 2 14
      ]
    -- Compact A-Z LCARS touch keyboard (7 cols × 4 rows)
    let kbY := sugY + 174
    let letters := "ABCDEFGHIJKLMNOPQRSTUVWXYZ".toList.toArray
    let keyGap := 6
    let keyW := (cw - 6 * keyGap) / 7
    let keyH := 54
    for i in [0:letters.size] do
      let col := i % 7; let row := i / 7
      let ch' := letters[i]!
      cmds := cmds ++ [
        .button (.restoreLetter ch')
          { x := cx + col * (keyW + keyGap), y := kbY + row * (keyH + keyGap), w := keyW, h := keyH }
          (String.singleton ch') pal.surface pal.highlight 3 12
      ]
    -- Backspace / Pop Word / Submit bar
    let actY := kbY + 4 * (keyH + keyGap) + 12
    let thirdW := (cw - 16) / 3
    cmds := cmds ++ [
      .button .restoreBackspace { x := cx, y := actY, w := thirdW, h := 66 } "DEL CHAR" pal.secondary pal.pillFg 2 16,
      .button .restorePopWord { x := cx + thirdW + 8, y := actY, w := thirdW, h := 66 } "UNDO WORD" pal.secondary pal.pillFg 2 16,
      .button .restoreSubmit { x := cx + 2 * (thirdW + 8), y := actY, w := thirdW, h := 66 }
        (if entered.size == 24 then "VERIFY 24" else s!"{entered.size}/24")
        (if entered.size == 24 then pal.ok else pal.surface)
        (if entered.size == 24 then pal.pillFg else Color.dimText) 2 16
    ]
    return cmds

  | .setupPin _ first? buf =>
    let prompt := match first? with
      | none => "CREATE 6-12 DIGIT ACCESS CODE"
      | some _ => "CONFIRM ACCESS CODE"
    [ .pill { x := cx, y := cy, w := cw, h := 58 } pal.surface 14,
      .text (cx + 14) (cy + 18) prompt 2 pal.primary ] ++
    pinPadCmds cx (cy + 74) cw pal buf.length "NEXT" ++
    [ .button .abortReview { x := cx, y := cy + ch - 68, w := cw, h := 62 } "ABORT SETUP" pal.alert Color.white 3 18 ]

  | .home =>
    let (fpStr, appStr) := match m.secrets with
      | some (id, _) => (id.fingerprintHex.toUpper, truncStr id.approverPubKeyHex.toUpper 20)
      | none => ("LOCKED", "LOCKED")
    let (wKind, wAddr) := match m.wallet with
      | some wal => (wal.kindLabel, truncStr wal.firstAddress 28)
      | none => ("NONE REGISTERED", "DROP INBOX/DESCRIPTOR.TXT")
    [ .pill { x := cx, y := cy, w := cw, h := 148 } pal.surface 16,
      .text (cx + 14) (cy + 14) s!"MASTER FP:  {fpStr}" 2 pal.highlight,
      .text (cx + 14) (cy + 42) s!"APPROVER:   {appStr}" 2 pal.accent,
      .text (cx + 14) (cy + 74) s!"WALLET:     {wKind}" 2 pal.primary,
      .text (cx + 14) (cy + 102) wAddr 2 pal.fg,
      .button .navInbox { x := cx, y := cy + 174, w := cw, h := 88 } "SCAN AIR-GAP INBOX" pal.primary pal.pillFg 3 22,
      .button .navKeys { x := cx, y := cy + 280, w := cw, h := 84 } "PUBLIC KEYS & QR" pal.accent pal.pillFg 3 22,
      .button .navDiag { x := cx, y := cy + 382, w := cw, h := 78 } "RUNTIME DIAGNOSTICS" pal.secondary pal.pillFg 3 22,
      .button .lockNow { x := cx, y := cy + ch - 84, w := cw, h := 78 } "LOCK & WIPE RAM" pal.alert Color.white 3 22 ]

  | .keys tab => Id.run do
    let thirdW := (cw - 16) / 3
    let mut cmds : List DrawCmd := [
      .button (.keysTab 0) { x := cx, y := cy, w := thirdW, h := 56 } "OVERRIDE"
        (if tab == 0 then pal.primary else pal.surface) (if tab == 0 then pal.pillFg else pal.fg) 2 14,
      .button (.keysTab 1) { x := cx + thirdW + 8, y := cy, w := thirdW, h := 56 } "APPROVER"
        (if tab == 1 then pal.primary else pal.surface) (if tab == 1 then pal.pillFg else pal.fg) 2 14,
      .button (.keysTab 2) { x := cx + 2 * (thirdW + 8), y := cy, w := thirdW, h := 56 } "ADDR 0"
        (if tab == 2 then pal.primary else pal.surface) (if tab == 2 then pal.pillFg else pal.fg) 2 14
    ]
    let (hdr, payload) := match m.secrets, tab with
      | some (id, _), 0 => ("OVERRIDE XPUB EXPRESSION", id.overrideKeyExpression)
      | some (id, _), 1 => ("APPROVER X-ONLY PUBKEY", id.approverPubKeyHex)
      | _, _ =>
        match m.wallet with
        | some wal => (s!"{wal.kindLabel} RECEIVE #0", wal.firstAddress)
        | none => ("NO WALLET REGISTERED", "")
    cmds := cmds ++ [.text cx (cy + 70) hdr 2 pal.highlight]
    if let some qr := Qr.encode payload then
      if !payload.isEmpty then
        cmds := cmds ++ [.qr { x := cx, y := cy + 98, w := cw, h := 330 } qr]
    let lines := wrapLines payload 32 4
    let mut ly := cy + 444
    for ln in lines do
      cmds := cmds ++ [.text cx ly ln 2 pal.fg]
      ly := ly + 22
    let btnY := cy + ch - 80
    let halfW := (cw - 12) / 2
    cmds := cmds ++ [
      .button .navHome { x := cx, y := btnY, w := halfW, h := 74 } "BRIDGE" pal.secondary pal.pillFg 3 20,
      .button .exportKeys { x := cx + halfW + 12, y := btnY, w := halfW, h := 74 } "EXPORT FILE" pal.primary pal.pillFg 3 20
    ]
    return cmds

  | .inbox entries => Id.run do
    let mut cmds : List DrawCmd := [
      .text cx cy "DROP DESCRIPTOR / PSBT IN INBOX/" 2 pal.accent
    ]
    if entries.isEmpty then
      cmds := cmds ++ [
        .pill { x := cx, y := cy + 40, w := cw, h := 130 } pal.surface 16,
        .text (cx + 14) (cy + 62) "NO FILES DETECTED" 3 Color.dimText,
        .text (cx + 14) (cy + 104) "INBOX/DESCRIPTOR.TXT | PSBT.B64" 2 pal.fg,
        .text (cx + 14) (cy + 130) "INBOX/APPROVE.B64" 2 pal.fg
      ]
    else
      let maxShow := min 6 entries.size
      for i in [0:maxShow] do
        let e := entries[i]!
        let kindTag := match e.kind with
          | .descriptor => "[DESC] "
          | .overridePsbt => "[PSBT] "
          | .approvePsbt => "[APPR] "
        let col := match e.kind with
          | .descriptor => pal.secondary
          | .overridePsbt => pal.primary
          | .approvePsbt => pal.accent
        cmds := cmds ++ [
          .button (.openInboxItem i) { x := cx, y := cy + 36 + i * 82, w := cw, h := 72 }
            (truncStr (kindTag ++ e.fileName.toUpper) 26) col pal.pillFg 2 18
        ]
    let btnY := cy + ch - 80
    let halfW := (cw - 12) / 2
    cmds := cmds ++ [
      .button .navHome { x := cx, y := btnY, w := halfW, h := 74 } "BRIDGE" pal.secondary pal.pillFg 3 20,
      .button .scanInbox { x := cx + halfW + 12, y := btnY, w := halfW, h := 74 } "RESCAN" pal.primary pal.pillFg 3 20
    ]
    return cmds

  | .reviewDescriptor fileName wal => Id.run do
    let mut cmds : List DrawCmd := [
      .pill { x := cx, y := cy, w := cw, h := 300 } pal.surface 16,
      .text (cx + 14) (cy + 16) s!"FILE: {truncStr fileName.toUpper 24}" 2 Color.dimText,
      .text (cx + 14) (cy + 46) wal.kindLabel 3 pal.highlight,
      .text (cx + 14) (cy + 88) "VERIFY RECEIVE ADDRESS #0:" 2 pal.primary
    ]
    let addrLines := wrapLines wal.firstAddress 30 3
    let mut ay := cy + 118
    for ln in addrLines do
      cmds := cmds ++ [.text (cx + 14) ay ln 2 pal.ok]
      ay := ay + 24
    cmds := cmds ++ [
      .text (cx + 14) (cy + 206) "OUR OVERRIDE KEY: VERIFIED" 2 pal.ok,
      .text (cx + 14) (cy + 236) s!"THRESHOLD: {wal.threshold} OF {wal.keyCount} KEYS" 2 pal.fg,
      .text (cx + 14) (cy + 266) "CHECKSUM: VALID" 2 pal.fg
    ]
    let btnY := cy + ch - 84
    let halfW := (cw - 12) / 2
    cmds := cmds ++ [
      .button .abortReview { x := cx, y := btnY, w := halfW, h := 78 } "ABORT" pal.alert Color.white 3 20,
      .button .registerWallet { x := cx + halfW + 12, y := btnY, w := halfW, h := 78 } "REGISTER" pal.ok pal.pillFg 3 20
    ]
    return cmds

  | .reviewTx tx armed => Id.run do
    let mut cmds : List DrawCmd := [
      .pill { x := cx, y := cy, w := cw, h := 132 } pal.surface 14,
      .text (cx + 12) (cy + 12) tx.roleLabel 2 pal.primary,
      .text (cx + 12) (cy + 38) s!"TXID: {truncStr tx.txidDisplay 26}" 2 pal.fg,
      .text (cx + 12) (cy + 66)
        (match tx.leaving with
         | some lv => s!"LEAVING: {formatSats lv}"
         | none => s!"INPUTS: {tx.inputCount} (APPROVER MODE)") 2 pal.highlight,
      .text (cx + 12) (cy + 94)
        (match tx.fee with
         | some fee => s!"FEE: {formatSats fee}  IN: {tx.inputCount}"
         | none => s!"OUTPUTS: {tx.outputs.size}") 2 pal.accent
    ]
    let maxOuts := min 4 tx.outputs.size
    let mut oy := cy + 148
    for i in [0:maxOuts] do
      let o := tx.outputs[i]!
      let badge := if o.isChange then "CHANGE (OURS)" else "EXTERNAL PAY"
      let bCol := if o.isChange then pal.ok else pal.alert
      let addrLines := wrapLines o.address 30 2
      cmds := cmds ++ [
        .pill { x := cx, y := oy, w := cw, h := 104 } pal.surface 12,
        .text (cx + 12) (oy + 10) s!"OUT {i + 1}: {badge}" 2 bCol,
        .text (cx + 12) (oy + 36) (formatSats o.sats) 2 pal.highlight,
        .text (cx + 12) (oy + 62) (addrLines[0]?.getD "") 2 pal.fg,
        .text (cx + 12) (oy + 82) (addrLines[1]?.getD "") 2 pal.fg
      ]
      oy := oy + 114
    let btnY := cy + ch - 84
    let halfW := (cw - 12) / 2
    if !armed then
      cmds := cmds ++ [
        .button .abortReview { x := cx, y := btnY, w := halfW, h := 78 } "ABORT" pal.secondary pal.pillFg 3 20,
        .button .armSign { x := cx + halfW + 12, y := btnY, w := halfW, h := 78 } "ARM SIGNER" pal.primary pal.pillFg 3 20
      ]
    else
      cmds := cmds ++ [
        .button .abortReview { x := cx, y := btnY, w := halfW, h := 78 } "CANCEL" pal.secondary pal.pillFg 3 20,
        .button .confirmSign { x := cx + halfW + 12, y := btnY, w := halfW, h := 78 } "SIGN NOW" pal.alert Color.white 3 20
      ]
    return cmds

  | .signed res => Id.run do
    let mut cmds : List DrawCmd := [
      .pill { x := cx, y := cy, w := cw, h := 112 } pal.surface 14,
      .text (cx + 12) (cy + 14) res.summary 2 pal.ok,
      .text (cx + 12) (cy + 44) s!"TXID: {truncStr res.txidDisplay 26}" 2 pal.fg,
      .text (cx + 12) (cy + 74) s!"OUT:  {res.outFileName.toUpper}" 2 pal.accent
    ]
    if let some qr := Qr.encode res.payloadText then
      cmds := cmds ++ [.qr { x := cx, y := cy + 128, w := cw, h := 350 } qr]
    else
      cmds := cmds ++ [
        .pill { x := cx, y := cy + 128, w := cw, h := 120 } pal.surface 14,
        .text (cx + 14) (cy + 160) "PSBT EXCEEDS SINGLE QR CAPACITY" 2 pal.accent,
        .text (cx + 14) (cy + 190) "RETRIEVE FROM OUTBOX FILE" 2 pal.fg
      ]
    let btnY := cy + ch - 80
    let halfW := (cw - 12) / 2
    cmds := cmds ++ [
      .button .navHome { x := cx, y := btnY, w := halfW, h := 74 } "BRIDGE" pal.primary pal.pillFg 3 20,
      .button .lockNow { x := cx + halfW + 12, y := btnY, w := halfW, h := 74 } "LOCK NOW" pal.alert Color.white 3 20
    ]
    return cmds

  | .diagnostics digest bigOk entropyHex =>
    let bigStr := match bigOk with
      | none => "NOT RUN YET"
      | some true => "PASS (216K CHECKS)"
      | some false => "FAILED"
    let bigCol := match bigOk with
      | some true => pal.ok
      | some false => pal.alert
      | none => Color.dimText
    [ .pill { x := cx, y := cy, w := cw, h := 240 } pal.surface 16,
      .text (cx + 14) (cy + 16) "VERIFIED MINIMAL RUNTIME" 2 pal.primary,
      .text (cx + 14) (cy + 48) "SELF-TEST DIGEST:" 2 pal.accent,
      .text (cx + 14) (cy + 74) (truncStr digest 30) 2 pal.ok,
      .text (cx + 14) (cy + 110) s!"BIG-NUMBERS: {bigStr}" 2 bigCol,
      .text (cx + 14) (cy + 144) "OS GETRANDOM SAMPLE:" 2 pal.accent,
      .text (cx + 14) (cy + 170) (truncStr entropyHex 30) 2 pal.fg,
      .text (cx + 14) (cy + 204) "ALLOCATOR: MINI/ALLOC ZERO-ON-FREE" 2 Color.dimText,
      .button .runSelfTest { x := cx, y := cy + 266, w := cw, h := 74 } "RE-RUN SELF-TEST & ENTROPY" pal.primary pal.pillFg 2 20,
      .button .runBigTest { x := cx, y := cy + 356, w := cw, h := 74 } "RUN BIG-NUMBER VERIFY" pal.accent pal.pillFg 2 20,
      .button .navHome { x := cx, y := cy + ch - 80, w := cw, h := 74 } "RETURN TO BRIDGE" pal.secondary pal.pillFg 3 20 ]
  chrome ++ content

end Tricorder.Ui.View
