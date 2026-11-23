import Platform
import Tricorder.App
import Tricorder.Ui.Frame
import Tricorder.Ui.Layout
import Tricorder.Ui.State
import Tricorder.Ui.View
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign
import Tests.Fixture

/-! # Headless tap-journey test & Screenshot Renderer

Runs the real `Tricorder.App` session on macOS (both Lean runtime and minimal runtime):
1. Verifies `buttonsDisjoint` on every screen visited (proving no overlapping LCARS touch targets).
2. Drives tap coordinates directly through `hitTest` (center of each rendered button rect):
   SetupChoice -> Generate 24 Words -> Page 2 -> Set PIN -> Confirm PIN -> Home ->
   Keys & QR (tabs 0, 1, 2) -> Diagnostics (SelfTest + BigTest) -> Inbox ->
   Register Taproot Descriptor -> Approve PSBT -> Arm -> Confirm Sign -> Signed + QR ->
   Lock / Background Pause -> 10 Wrong PINs Auto-Wipe!
3. Exports binary `.ppm` screenshots to `TRICORDER_SHOTS_DIR` (if set via argv) for visual inspection
   and external QR scanner verification. -/

open Tricorder Tricorder.Ui Tricorder.Signer Winnow Winnow.Keys

private def println (s : String) : IO Unit := Platform.write (s ++ "\n").toUTF8

private def findButtonCenter? (cmds : List DrawCmd) (target : ButtonId) : Option (Nat × Nat) :=
  (buttonsOf cmds).find? (·.1 == target) |>.map fun (_, r) => (r.x + r.w / 2, r.y + r.h / 2)

private def tapBtn (s : App.Session) (target : ButtonId) : IO App.Session := do
  let some (cx, cy) := findButtonCenter? s.cmds target
    | throw (IO.userError s!"button {repr target} not found on current screen")
  let hit := hitTest s.cmds cx cy
  unless hit == some target do
    throw (IO.userError s!"hitTest ({cx},{cy}) returned {repr hit}, expected {repr target}")
  App.dispatch s (.tapButton target)

/-- Whether the screen shows `address` whole: its lines of text, one after another, contain it. -/
private def wholeAddress (ses : App.Session) (address : String) : Bool :=
  let texts := ses.cmds.filterMap fun cmd =>
    match cmd with
    | .text _ _ t _ _ => some t
    | _ => none
  ((String.join texts).splitOn address).length > 1

private def saveShot (dir? : Option String) (name : String) (s : App.Session) : IO Unit := do
  if let some dir := dir? then
    let frame := renderCmds s.width s.height s.model.network.palette.bg s.cmds
    Platform.writeFile s!"{dir}/{name}.ppm" frame.toPpm

def main (args : List String) : IO UInt32 := do
  let shotDir? := match args with
    | [d] => some d
    | _ => none
  let mut failures := 0
  let check (name : String) (ok : Bool) : IO Unit := do
    if ok then println s!"ok    {name}"
    else println s!"FAIL  {name}"
  -- Start clean
  Platform.deleteFile Vault.vaultFile
  Platform.deleteFile Vault.attemptsFile
  Platform.deleteFile Vault.descriptorFile

  let mut s ← App.startSession .signet 540 1200 64 44
  let checkDisjoint (label : String) (ses : App.Session) : IO Bool := do
    let d := buttonsDisjoint ses.cmds
    check s!"buttons disjoint: {label}" d
    return d

  if !(← checkDisjoint "setupChoice" s) then failures := failures + 1
  saveShot shotDir? "01_setup_choice" s

  -- 1. Generate 24 words
  s ← tapBtn s .setupGenerate
  if !(← checkDisjoint "setupWords page 1" s) then failures := failures + 1
  saveShot shotDir? "02_setup_words_p1" s
  s ← tapBtn s .setupNextPage
  if !(← checkDisjoint "setupWords page 2" s) then failures := failures + 1
  s ← tapBtn s .setupToPin
  if !(← checkDisjoint "setupPin" s) then failures := failures + 1
  saveShot shotDir? "03_setup_pin" s

  -- 2. Enter PIN 170147 twice to seal vault.bin
  for d in [1, 7, 0, 1, 4, 7] do s ← tapBtn s (.pinDigit d)
  s ← tapBtn s .pinSubmit
  for d in [1, 7, 0, 1, 4, 7] do s ← tapBtn s (.pinDigit d)
  s ← tapBtn s .pinSubmit

  let unlockedOk := s.model.secrets.isSome && match s.model.screen with | .home => true | _ => false
  check "vault sealed and unlocked onto the home screen" unlockedOk
  if !unlockedOk then failures := failures + 1
  if !(← checkDisjoint "home" s) then failures := failures + 1
  saveShot shotDir? "04_home" s

  -- 3. Keys & QR screen
  s ← tapBtn s .navKeys
  if !(← checkDisjoint "keys tab 0" s) then failures := failures + 1
  saveShot shotDir? "05_keys_qr_override" s
  s ← tapBtn s (.keysTab 1)
  saveShot shotDir? "06_keys_qr_address" s
  s ← tapBtn s .exportKeys
  s ← tapBtn s .navHome

  -- 4. Diagnostics screen (runs SelfTest + BigTest on-device!)
  s ← tapBtn s .navDiag
  if !(← checkDisjoint "diagnostics" s) then failures := failures + 1
  s ← tapBtn s .runBigTest
  let diagOk := match s.model.screen with | .diagnostics dig (some true) _ => !dig.isEmpty | _ => false
  check "diagnostics SelfTest + BigTest pass" diagOk
  if !diagOk then failures := failures + 1
  saveShot shotDir? "07_diagnostics" s
  s ← tapBtn s .navHome

  -- 5. Drop a descriptor and a payment of five outputs into inbox/, review every page and sign
  let some (idA, _) := s.model.secrets | do println "FAIL missing identity"; return 1
  let entB := ByteArray.mk ((Array.range 32).map (fun i => (i + 11).toUInt8))
  let entC := ByteArray.mk ((Array.range 32).map (fun i => (i + 77).toUInt8))
  let .ok wB := Bip39Ascii.fromEntropy entB | return 1
  let .ok wC := Bip39Ascii.fromEntropy entC | return 1
  let .ok idB := Identity.ofWords wB .signet | return 1
  let .ok idC := Identity.ofWords wC .signet | return 1
  let .ok (_, psbt, _) := Tests.Fixture.overridePayment idA idB idC 5 190000
    | do println "FAIL no payment for the test"; return 1
  Platform.writeFile "inbox/descriptor.txt" (Tests.Fixture.descriptor idA idB idC).toUTF8

  s ← tapBtn s .navInbox
  if !(← checkDisjoint "inbox" s) then failures := failures + 1
  s ← tapBtn s (.openInboxItem 0)
  if !(← checkDisjoint "reviewDescriptor" s) then failures := failures + 1
  saveShot shotDir? "08_review_descriptor" s
  s ← tapBtn s .registerWallet
  let regOk := s.model.wallet.isSome
  check "descriptor registered via UI review" regOk
  if !regOk then failures := failures + 1

  Platform.writeFile "inbox/payment.b64" psbt.base64.toUTF8
  s ← tapBtn s .navInbox
  let paymentIdx := match s.model.screen with
    | .inbox entries => (entries.findIdx? (·.fileName == "payment.b64")).getD 0
    | _ => 0
  s ← tapBtn s (.openInboxItem paymentIdx)
  if !(← checkDisjoint "reviewTx page 1" s) then failures := failures + 1
  saveShot shotDir? "09_review_tx" s

  -- The first page of two offers no arming, shows outputs 1 to 3 with their addresses whole, and the signer
  -- cannot be armed from it even by an event the screen does not offer.
  let outAddresses : Array String := match s.model.screen with
    | .reviewTx tx _ => tx.outputs.map fun (o : ReviewedOutput) => o.address
    | _ => #[]
  let firstPageOk := outAddresses.size == 5 &&
    (buttonsOf s.cmds).all (·.1 != .armSign) &&
    (List.range 3).all (fun k => wholeAddress s outAddresses[k]!) && !wholeAddress s outAddresses[3]!
  check "page 1 of 2 shows outputs 1 to 3 whole and offers no arming" firstPageOk
  if !firstPageOk then failures := failures + 1
  let forced ← App.dispatch s (.tapButton .armSign)
  let notArmed := match forced.model.screen with | .reviewTx _ false => true | _ => false
  check "the signer is not armed before the last page is reached" notArmed
  if !notArmed then failures := failures + 1

  s ← tapBtn s .reviewNextPage
  if !(← checkDisjoint "reviewTx page 2" s) then failures := failures + 1
  let lastPageOk := wholeAddress s outAddresses[3]! && wholeAddress s outAddresses[4]! && !wholeAddress s outAddresses[0]!
  check "page 2 of 2 shows outputs 4 and 5 whole" lastPageOk
  if !lastPageOk then failures := failures + 1
  s ← tapBtn s .armSign
  if !(← checkDisjoint "reviewTx armed" s) then failures := failures + 1
  saveShot shotDir? "10_review_tx_armed" s
  s ← tapBtn s .confirmSign
  if !(← checkDisjoint "signed" s) then failures := failures + 1
  saveShot shotDir? "11_signed_qr" s

  let signedOk := match s.model.screen with
    | .signed res =>
      match PSBT.ofBase64 res.payloadText with
      | .ok signed => (signed.inputs[0]?.map fun i => i.partialSignatures.size == 1).getD false
      | .error _ => false
    | _ => false
  check "reading both pages, arming and confirming signs the payment with the override key" signedOk
  if !signedOk then failures := failures + 1

  -- 6. Background pause wipes RAM secrets immediately!
  s ← App.dispatch s .appPaused
  let pauseOk := s.model.secrets.isNone && match s.model.screen with | .locked => true | _ => false
  check "appPaused wipes secrets and locks screen" pauseOk
  if !pauseOk then failures := failures + 1
  if !(← checkDisjoint "locked PIN pad" s) then failures := failures + 1
  saveShot shotDir? "12_locked_pin" s

  -- 7. Unlock again with right PIN
  for d in [1, 7, 0, 1, 4, 7] do s ← tapBtn s (.pinDigit d)
  s ← tapBtn s .pinSubmit
  let relockOk := s.model.secrets.isSome && s.model.wallet.isSome
  check "unlocks persisted vault and restores registered wallet" relockOk
  if !relockOk then failures := failures + 1

  -- 8. Lock and fail PIN 10 times -> auto-wipe!
  s ← tapBtn s .lockNow
  for _ in [0:10] do
    for d in [9, 9, 9, 9, 9, 9] do s ← tapBtn s (.pinDigit d)
    s ← tapBtn s .pinSubmit
  let vaultAfterWipe ← Platform.readFile? Vault.vaultFile
  let wipedOk := !s.model.hasVault && s.model.secrets.isNone && vaultAfterWipe.isNone &&
    match s.model.screen with | .setupChoice => true | _ => false
  check "10 wrong PINs automatically wipes vault.bin and returns to setup" wipedOk
  if !wipedOk then failures := failures + 1

  -- Cleanup inbox/outbox
  Platform.deleteFile "inbox/descriptor.txt"
  Platform.deleteFile "inbox/payment.b64"

  if failures == 0 then
    println "journey-test: all checks passed"
    return 0
  else
    println s!"journey-test: {failures} failed"
    return 1
