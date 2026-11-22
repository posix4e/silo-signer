import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Tricorder.Crypto.Vault
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign
import Tricorder.Signer.Protocol
import Tricorder.Ui.Layout

/-! # Pure Elm-style State Machine for Tricorder

Security invariants proved in `Tricorder/Proofs/StateProofs.lean`:
1. Whenever Tricorder is on a locked or setup screen (or after `appPaused` / 10 wrong PINs),
   `model.secrets = none` (no unlocked `Identity` or seed words reside in the model).
2. `Event.appPaused` ALWAYS wipes `secrets`, clears `pinInput`, and emits no signing effect.
3. `Effect.executeSign tx` can ONLY be emitted when `model.secrets.isSome`, `model.screen = .reviewTx tx true`
   (armed after reviewing `tx`), and the user explicitly taps `ButtonId.confirmSign`. -/

namespace Tricorder.Ui

open Tricorder.Signer

inductive Screen where
  | locked
  | setupChoice
  | setupWords (words : Array String) (page : Nat)
  | setupRestore (entered : Array String) (prefixBuf : String)
  | setupPin (words : Array String) (firstPin? : Option String) (pinBuf : String)
  | home
  | keys (tab : Nat)
  | inbox (entries : Array Protocol.InboxEntry)
  | reviewDescriptor (fileName : String) (wallet : RegisteredWallet)
  | reviewTx (tx : ReviewedTx) (armed : Bool)
  | signed (res : SignedResult)
  | diagnostics (selfTestDigest : String) (bigTestOk : Option Bool) (entropyHex : String)

def Screen.isLockedOrSetup : Screen → Bool
  | .locked | .setupChoice | .setupWords .. | .setupRestore .. | .setupPin .. => true
  | _ => false

structure Model where
  network : Network
  hasVault : Bool
  failedAttempts : Nat
  pinInput : String
  screen : Screen
  /-- Present ONLY while unlocked on an active session screen; cleared on Lock, Pause, or Wipe. -/
  secrets : Option (Identity × Array String)
  wallet : Option RegisteredWallet
  statusMsg : String
  isError : Bool
  /-- Which page of the outputs the transaction review screen is showing, from 0. -/
  reviewPage : Nat := 0

inductive Effect where
  | generateSeed
  | sealVault (pin : String) (words : Array String)
  | unlockVault (pin : String)
  | wipeVault
  | scanInbox
  | loadInboxItem (entry : Protocol.InboxEntry)
  | saveDescriptor (descriptor : String)
  | exportKeys (content : String)
  | executeSign (tx : ReviewedTx)
  | runDiagnostics (runBig : Bool)

def Effect.isSign : Effect → Bool
  | .executeSign _ => true
  | _ => false

inductive Event where
  | tapButton (id : ButtonId)
  | appPaused
  | hostSeedGenerated (words : Array String)
  | hostVaultSealed (words : Array String) (id : Identity)
  | hostUnlockOk (words : Array String) (id : Identity) (wallet? : Option RegisteredWallet)
  | hostUnlockFailed (attempts : Nat) (wiped : Bool)
  | hostInboxLoaded (entries : Array Protocol.InboxEntry)
  | hostDescriptorReviewed (fileName : String) (wallet : RegisteredWallet)
  | hostTxReviewed (tx : ReviewedTx)
  | hostSigned (res : SignedResult)
  | hostDiagnostics (digest : String) (bigOk : Option Bool) (entropyHex : String)
  | hostStatus (msg : String) (isError : Bool)

def Model.initial (network : Network) (hasVault : Bool) (failedAttempts : Nat) : Model :=
  let wiped := failedAttempts ≥ Vault.maxFailedAttempts
  let effectiveHasVault := hasVault && !wiped
  { network
    hasVault := effectiveHasVault
    failedAttempts := if wiped then 0 else failedAttempts
    pinInput := ""
    screen := if effectiveHasVault then .locked else .setupChoice
    secrets := none
    wallet := none
    statusMsg := if effectiveHasVault then "ENTER ACCESS CODE" else "NO VAULT - INITIALIZE KEY"
    isError := false }

private def dropLastChar (s : String) : String :=
  let cs := s.toList
  if cs.isEmpty then "" else String.ofList cs.dropLast

/-- Immediate wipe of unlocked in-memory secrets and PIN buffer (used by Lock and `appPaused`). -/
def lockModel (m : Model) (msg : String) : Model :=
  { m with
    pinInput := ""
    secrets := none
    wallet := none
    screen := if m.hasVault then .locked else .setupChoice
    statusMsg := msg
    isError := false }

def updateTap (m : Model) (btn : ButtonId) : Model × List Effect :=
  match m.screen, btn with
  -- Locked PIN pad
  | .locked, .pinDigit d =>
    if m.pinInput.length < Vault.maxPinLength && d < 10 then
      ({ m with pinInput := m.pinInput ++ toString d, statusMsg := "ENTER ACCESS CODE", isError := false }, [])
    else (m, [])
  | .locked, .pinBackspace =>
    ({ m with pinInput := dropLastChar m.pinInput, isError := false }, [])
  | .locked, .pinSubmit =>
    if !Vault.validPin m.pinInput then
      ({ m with statusMsg := "PIN MUST BE 6 TO 12 DIGITS", isError := true }, [])
    else
      ({ m with pinInput := "", statusMsg := "DECRYPTING VAULT...", isError := false }, [.unlockVault m.pinInput])
  | .locked, .setupGenerate =>
    if !m.hasVault then
      ({ m with screen := .setupChoice, secrets := none, pinInput := "", statusMsg := "INITIALIZE KEY", isError := false }, [])
    else (m, [])

  -- First-run setup choice
  | .setupChoice, .setupGenerate =>
    ({ m with secrets := none, statusMsg := "DRAWING ENTROPY...", isError := false }, [.generateSeed])
  | .setupChoice, .setupRestore =>
    ({ m with screen := .setupRestore #[] "", secrets := none, statusMsg := "ENTER 24 BIP39 WORDS", isError := false }, [])

  -- Displaying generated 24 words (pages 0 and 1, 12 words per page)
  | .setupWords words page, .setupNextPage =>
    ({ m with screen := .setupWords words (min 1 (page + 1)), secrets := none }, [])
  | .setupWords words page, .setupPrevPage =>
    if page == 0 then
      ({ m with screen := .setupChoice, secrets := none, statusMsg := "INITIALIZE KEY", isError := false }, [])
    else
      ({ m with screen := .setupWords words (page - 1), secrets := none }, [])
  | .setupWords words _, .setupToPin =>
    ({ m with screen := .setupPin words none "", secrets := none, statusMsg := "CHOOSE 6-12 DIGIT PIN", isError := false }, [])

  -- On-screen 24-word BIP39 restore
  | .setupRestore entered pref, .restoreLetter c =>
    if entered.size < 24 && pref.length < 8 then
      ({ m with screen := .setupRestore entered (pref.push c), secrets := none, isError := false }, [])
    else (m, [])
  | .setupRestore entered pref, .restoreBackspace =>
    ({ m with screen := .setupRestore entered (dropLastChar pref), secrets := none, isError := false }, [])
  | .setupRestore entered _, .restoreClear =>
    ({ m with screen := .setupRestore entered "", secrets := none, isError := false }, [])
  | .setupRestore entered _, .restorePickWord w =>
    if entered.size < 24 then
      let next := entered.push w
      ({ m with screen := .setupRestore next "", secrets := none, statusMsg := s!"{next.size}/24 WORDS ENTERED", isError := false }, [])
    else (m, [])
  | .setupRestore entered _, .restorePopWord =>
    if entered.size > 0 then
      let next := entered.pop
      ({ m with screen := .setupRestore next "", secrets := none, statusMsg := s!"{next.size}/24 WORDS ENTERED", isError := false }, [])
    else
      ({ m with screen := .setupChoice, secrets := none, statusMsg := "INITIALIZE KEY", isError := false }, [])
  | .setupRestore entered _, .restoreSubmit =>
    match Bip39Ascii.validate entered with
    | .ok _ =>
      ({ m with screen := .setupPin entered none "", secrets := none, statusMsg := "CHOOSE 6-12 DIGIT PIN", isError := false }, [])
    | .error err =>
      ({ m with secrets := none, statusMsg := err.toUpper, isError := true }, [])

  -- Choosing & confirming PIN to seal vault.bin
  | .setupPin words first? buf, .pinDigit d =>
    if buf.length < Vault.maxPinLength && d < 10 then
      ({ m with screen := .setupPin words first? (buf ++ toString d), secrets := none, isError := false }, [])
    else (m, [])
  | .setupPin words first? buf, .pinBackspace =>
    ({ m with screen := .setupPin words first? (dropLastChar buf), secrets := none, isError := false }, [])
  | .setupPin words none buf, .pinSubmit =>
    if !Vault.validPin buf then
      ({ m with secrets := none, statusMsg := "PIN MUST BE 6 TO 12 DIGITS", isError := true }, [])
    else
      ({ m with screen := .setupPin words (some buf) "", secrets := none, statusMsg := "RE-ENTER PIN TO CONFIRM", isError := false }, [])
  | .setupPin words (some first) buf, .pinSubmit =>
    if buf != first then
      ({ m with screen := .setupPin words none "", secrets := none, statusMsg := "PINS DID NOT MATCH - RETRY", isError := true }, [])
    else
      ({ m with screen := .setupPin words none "", secrets := none, statusMsg := "SEALING VAULT...", isError := false }, [.sealVault first words])
  | .setupPin _ _ _, .abortReview =>
    ({ m with screen := .setupChoice, secrets := none, statusMsg := "SETUP CANCELLED", isError := false }, [])

  -- Unlocked screens (only active when `m.secrets` is `some`)
  | _, .lockNow =>
    (lockModel m "SIGNER LOCKED", [])

  | _, .navHome =>
    match m.secrets with
    | some _ => ({ m with screen := .home, statusMsg := "STANDBY - OFFLINE", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | _, .navKeys =>
    match m.secrets with
    | some _ => ({ m with screen := .keys 0, statusMsg := "PUBLIC KEYS - SAFE TO SHARE", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | _, .navInbox =>
    match m.secrets with
    | some _ => ({ m with screen := .inbox #[], statusMsg := "SCANNING INBOX...", isError := false }, [.scanInbox])
    | none => (lockModel m "LOCKED", [])

  | _, .navDiag =>
    match m.secrets with
    | some _ =>
      ({ m with screen := .diagnostics "PENDING" none "", statusMsg := "RUNNING SELF-TEST...", isError := false },
       [.runDiagnostics false])
    | none => (lockModel m "LOCKED", [])

  | .keys _, .keysTab t =>
    match m.secrets with
    | some _ => ({ m with screen := .keys (min 1 t), isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | .keys _, .exportKeys =>
    match m.secrets with
    | some (id, _) =>
      let txt := Protocol.formatKeysExport id m.wallet
      ({ m with statusMsg := "EXPORTED TO OUTBOX/KEYS.TXT", isError := false }, [.exportKeys txt])
    | none => (lockModel m "LOCKED", [])

  | .inbox _, .scanInbox =>
    match m.secrets with
    | some _ => ({ m with statusMsg := "SCANNING INBOX...", isError := false }, [.scanInbox])
    | none => (lockModel m "LOCKED", [])

  | .inbox entries, .openInboxItem idx =>
    match m.secrets, entries[idx]? with
    | some _, some entry =>
      ({ m with statusMsg := s!"LOADING {entry.fileName.toUpper}...", isError := false }, [.loadInboxItem entry])
    | none, _ => (lockModel m "LOCKED", [])
    | _, none => (m, [])

  | .reviewDescriptor _ w, .registerWallet =>
    match m.secrets with
    | some _ =>
      ({ m with wallet := some w, screen := .home, statusMsg := s!"REGISTERED {w.kindLabel}", isError := false },
       [.saveDescriptor w.descriptor])
    | none => (lockModel m "LOCKED", [])

  | .reviewDescriptor _ _, .abortReview =>
    match m.secrets with
    | some _ => ({ m with screen := .home, statusMsg := "DESCRIPTOR ABORTED", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  -- Two-step transaction signing confirmation: ARM -> CONFIRM SIGN
  -- Every output is on some page, and the signer is armed only from the last one.
  | .reviewTx tx false, .reviewNextPage =>
    match m.secrets with
    | some _ =>
      let page := if tx.isLastPage m.reviewPage then m.reviewPage else m.reviewPage + 1
      ({ m with reviewPage := page, statusMsg := s!"OUTPUTS PAGE {page + 1} OF {tx.pageCount}", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | .reviewTx tx false, .reviewPrevPage =>
    match m.secrets with
    | some _ =>
      let page := m.reviewPage - 1
      ({ m with reviewPage := page, statusMsg := s!"OUTPUTS PAGE {page + 1} OF {tx.pageCount}", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | .reviewTx tx false, .armSign =>
    match m.secrets with
    | some _ =>
      -- Armed only from the last page of the outputs: before that, the answer is to read on.
      let last := tx.isLastPage m.reviewPage
      ({ m with
          screen := .reviewTx tx last
          statusMsg := if last then "ARMED - TAP CONFIRM TO SIGN" else "READ EVERY OUTPUT FIRST"
          isError := !last }, [])
    | none => (lockModel m "LOCKED", [])

  | .reviewTx tx true, .confirmSign =>
    match m.secrets with
    | some _ =>
      ({ m with statusMsg := "SIGNING WITH SECPCT...", isError := false }, [.executeSign tx])
    | none => (lockModel m "LOCKED", [])

  | .reviewTx _ _, .abortReview =>
    match m.secrets with
    | some _ => ({ m with screen := .home, statusMsg := "SIGNING ABORTED", isError := false }, [])
    | none => (lockModel m "LOCKED", [])

  | .diagnostics _ _ _, .runSelfTest =>
    match m.secrets with
    | some _ => ({ m with statusMsg := "RUNNING SELF-TEST...", isError := false }, [.runDiagnostics false])
    | none => (lockModel m "LOCKED", [])

  | .diagnostics _ _ _, .runBigTest =>
    match m.secrets with
    | some _ => ({ m with statusMsg := "RUNNING BIG-NUMBER TEST...", isError := false }, [.runDiagnostics true])
    | none => (lockModel m "LOCKED", [])

  | .diagnostics _ _ _, .drawEntropy =>
    match m.secrets with
    | some _ => ({ m with statusMsg := "SAMPLING HARDWARE RANDOM...", isError := false }, [.runDiagnostics false])
    | none => (lockModel m "LOCKED", [])

  | _, _ => (m, [])

def update (m : Model) (ev : Event) : Model × List Effect :=
  match ev with
  | .appPaused => (lockModel m "LOCKED ON BACKGROUND", [])
  | .tapButton btn => updateTap m btn
  | .hostSeedGenerated words =>
    ({ m with screen := .setupWords words 0, secrets := none, statusMsg := "RECORD 24 WORDS OFFLINE", isError := false }, [])
  | .hostVaultSealed words id =>
    ({ m with
        hasVault := true
        failedAttempts := 0
        pinInput := ""
        secrets := some (id, words)
        wallet := none
        screen := .home
        statusMsg := "VAULT SEALED - READY"
        isError := false }, [])
  | .hostUnlockOk words id wallet? =>
    ({ m with
        hasVault := true
        failedAttempts := 0
        pinInput := ""
        secrets := some (id, words)
        wallet := wallet?
        screen := .home
        statusMsg := "ACCESS GRANTED - OFFLINE"
        isError := false }, [])
  | .hostUnlockFailed attempts wiped =>
    if wiped || attempts ≥ Vault.maxFailedAttempts then
      ({ m with
          hasVault := false
          failedAttempts := 0
          pinInput := ""
          secrets := none
          wallet := none
          screen := .setupChoice
          statusMsg := "10 FAILED PINS - VAULT WIPED"
          isError := true }, [.wipeVault])
    else
      let left := Vault.maxFailedAttempts - attempts
      ({ m with
          failedAttempts := attempts
          pinInput := ""
          secrets := none
          screen := .locked
          statusMsg := s!"INVALID PIN - {left} LEFT BEFORE WIPE"
          isError := true }, [])
  | .hostInboxLoaded entries =>
    match m.secrets with
    | some _ =>
      let msg := if entries.isEmpty then "INBOX EMPTY - DROP FILES IN INBOX/" else s!"{entries.size} ITEM(S) IN INBOX"
      ({ m with screen := .inbox entries, statusMsg := msg, isError := false }, [])
    | none => (lockModel m "LOCKED", [])
  | .hostDescriptorReviewed fileName w =>
    match m.secrets with
    | some _ =>
      ({ m with screen := .reviewDescriptor fileName w, statusMsg := "VERIFY ADDRESS 0 ON WATCH WALLET", isError := false }, [])
    | none => (lockModel m "LOCKED", [])
  | .hostTxReviewed tx =>
    match m.secrets with
    | some _ =>
      ({ m with screen := .reviewTx tx false, reviewPage := 0, statusMsg := "INSPECT EVERY OUTPUT CAREFULLY", isError := false }, [])
    | none => (lockModel m "LOCKED", [])
  | .hostSigned res =>
    match m.secrets with
    | some _ =>
      ({ m with screen := .signed res, statusMsg := s!"SAVED {res.outFileName.toUpper}", isError := false }, [])
    | none => (lockModel m "LOCKED", [])
  | .hostDiagnostics digest bigOk entropyHex =>
    match m.secrets with
    | some _ =>
      ({ m with
          screen := .diagnostics digest bigOk entropyHex
          statusMsg := "DIAGNOSTICS COMPLETE"
          isError := false }, [])
    | none => (lockModel m "LOCKED", [])
  | .hostStatus msg isErr =>
    ({ m with statusMsg := msg.toUpper, isError := isErr }, [])

end Tricorder.Ui
