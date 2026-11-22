import Platform
import SelfTest
import Winnow.Crypto.Sha2
import Tricorder.BuildConfig
import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Tricorder.Crypto.Vault
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign
import Tricorder.Signer.Protocol
import Tricorder.Ui.Layout
import Tricorder.Ui.State
import Tricorder.Ui.View

/-! # Tricorder Hosted Session Driver

Single-threaded event loop driving `Ui.update`, `Ui.View.view`, and `Platform` effects for hosted
headless journey tests on macOS. Bare-metal execution uses `Tricorder/OsMain.lean` over `Kernel.Hw`
with zero filesystems. -/

namespace Tricorder.App

open Tricorder.Ui Tricorder.Signer

structure Session where
  model : Model
  width : Nat := 540
  height : Nat := 1200
  topInset : Nat := 64
  bottomInset : Nat := 44
  cmds : List DrawCmd := []

/-- Runs one pure-Lean self-test digest over `SelfTest.transcript`. -/
def selfTestDigestHex : String :=
  let h := Winnow.sha256 SelfTest.transcript
  hexBytes (h.extract 0 12)

/-- Runs `Effect` via `Platform` and returns the resulting host `Event`. -/
def performEffect (m : Model) (eff : Effect) : IO Event := do
  match eff with
  | .generateSeed =>
    let ent ← Platform.random 32
    match Bip39Ascii.fromEntropy ent with
    | .ok words => return .hostSeedGenerated words
    | .error err => return .hostStatus err true
  | .sealVault pin words =>
    let salt ← Platform.random 16
    let nonce ← Platform.random 12
    match Vault.sealVault m.network pin words salt nonce with
    | .error err => return .hostStatus err true
    | .ok blob =>
      match Identity.ofWords words m.network.toBitcoin with
      | .error err => return .hostStatus err true
      | .ok id =>
        Platform.writeFile Vault.vaultFile blob
        Platform.writeFile Vault.attemptsFile (Vault.encodeAttempts 0)
        Platform.writeFile Protocol.keysOutFile (Protocol.formatKeysExport id none).toUTF8
        return .hostVaultSealed words id
  | .unlockVault pin =>
    let some blob ← Platform.readFile? Vault.vaultFile
      | return .hostStatus "VAULT FILE MISSING" true
    -- The attempt is counted on disk before the PIN is tried, so that stopping the program buys no free guess.
    let nextAttempts := Vault.decodeAttempts (← Platform.readFile? Vault.attemptsFile) + 1
    Platform.writeFile Vault.attemptsFile (Vault.encodeAttempts nextAttempts)
    match Vault.openVault m.network pin blob with
    | .ok words =>
      match Identity.ofWords words m.network.toBitcoin with
      | .error err => return .hostStatus err true
      | .ok id =>
        Platform.writeFile Vault.attemptsFile (Vault.encodeAttempts 0)
        let wallet? ← match (← Platform.readFile? Vault.descriptorFile) with
          | none => pure none
          | some descBytes =>
            match String.fromUTF8? descBytes with
            | none => pure none
            | some txt => pure (registerDescriptor id txt).toOption
        Platform.writeFile Protocol.keysOutFile (Protocol.formatKeysExport id wallet?).toUTF8
        return .hostUnlockOk words id wallet?
    | .error _ =>
      if nextAttempts ≥ Vault.maxFailedAttempts then
        Platform.deleteFile Vault.vaultFile
        Platform.deleteFile Vault.descriptorFile
        Platform.deleteFile Vault.attemptsFile
        return .hostUnlockFailed nextAttempts true
      else
        return .hostUnlockFailed nextAttempts false
  | .wipeVault =>
    Platform.deleteFile Vault.vaultFile
    Platform.deleteFile Vault.descriptorFile
    Platform.deleteFile Vault.attemptsFile
    return .hostStatus "VAULT WIPED" true
  | .scanInbox =>
    let files ← Platform.listFiles Protocol.inboxDir
    let sorted := files.qsort (· < ·)
    let entries := sorted.filterMap Protocol.classifyInboxFile
    return .hostInboxLoaded entries
  | .loadInboxItem entry =>
    match m.secrets with
    | none => return .hostStatus "SIGNER LOCKED" true
    | some (id, _) =>
      let some raw ← Platform.readFile? entry.relPath
        | return .hostStatus s!"CANNOT READ {entry.fileName}" true
      match entry.kind with
      | .descriptor =>
        match String.fromUTF8? raw with
        | none => return .hostStatus "DESCRIPTOR NOT UTF-8" true
        | some txt =>
          match registerDescriptor id txt with
          | .ok w => return .hostDescriptorReviewed entry.fileName w
          | .error err => return .hostStatus err true
      | .overridePsbt =>
        match m.wallet with
        | none => return .hostStatus "REGISTER DESCRIPTOR FIRST" true
        | some w =>
          match parsePsbtBytes raw with
          | .error err => return .hostStatus err true
          | .ok psbt =>
            match reviewOverride id w psbt entry.fileName with
            | .ok rev => return .hostTxReviewed rev
            | .error err => return .hostStatus err true
  | .saveDescriptor desc =>
    Platform.writeFile Vault.descriptorFile desc.toUTF8
    if let some (id, _) := m.secrets then
      let w? := (registerDescriptor id desc).toOption
      Platform.writeFile Protocol.keysOutFile (Protocol.formatKeysExport id w?).toUTF8
    return .hostStatus "WALLET DESCRIPTOR SAVED" false
  | .exportKeys content =>
    Platform.writeFile Protocol.keysOutFile content.toUTF8
    return .hostStatus "EXPORTED TO OUTBOX/KEYS.TXT" false
  | .executeSign tx =>
    match m.secrets with
    | none => return .hostStatus "REFUSED: LOCKED" true
    | some (id, _) =>
      let fresh ← Platform.random 32
      match signReviewed id tx fresh with
      | .error err => return .hostStatus err true
      | .ok res =>
        Platform.writeFile res.outFileName (res.payloadText ++ "\n").toUTF8
        return .hostSigned res
  | .runDiagnostics runBig =>
    let dig := selfTestDigestHex
    let bigOk : Option Bool :=
      if runBig then
        -- Exercise big-number multiplication, division, modulo, and signed Int arithmetic on-device.
        let a : Nat := (1 <<< 256) + 0x170147
        let b : Nat := (1 <<< 129) + 1701
        let q := (a * b + 47) / b
        let r := (a * b + 47) % b
        let s : Int := -((1 : Int) <<< 200) - 99
        let t : Int := (1 : Int) <<< 97 + 7
        some (q == a && r == 47 && (s / t) * t + (s % t) == s)
      else none
    let ent ← Platform.random 12
    return .hostDiagnostics dig bigOk (hexBytes ent).toUpper

/-- Feeds an event into `Session`, running any emitted effects to quiescence (bounded to 4 steps). -/
def dispatch (s : Session) (ev : Event) : IO Session := do
  let mut cur := s.model
  let mut queue : List Event := [ev]
  let mut fuel := 4
  while fuel > 0 do
    match queue with
    | [] => break
    | e :: rest =>
      queue := rest
      let (next, effs) := update cur e
      cur := next
      for eff in effs do
        let reply ← performEffect cur eff
        queue := queue ++ [reply]
      fuel := fuel - 1
  let cmds := View.view cur s.width s.height s.topInset s.bottomInset
  return { s with model := cur, cmds }

def startSession (net : Network) (w h topInset bottomInset : Nat) : IO Session := do
  let vault? ← Platform.readFile? Vault.vaultFile
  let attempts := Vault.decodeAttempts (← Platform.readFile? Vault.attemptsFile)
  let initModel := Model.initial net vault?.isSome attempts
  let cmds := View.view initModel w h topInset bottomInset
  return { model := initModel, width := w, height := h, topInset, bottomInset, cmds }

end Tricorder.App
