import WinnowCore
import Winnow.Wallet.PSBTRoles
import Secp.Sha256
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor

/-! # Transaction and PSBT Review (Override & Approver roles)

Every byte of a PSBT is parsed and checked in Lean before anything is displayed or signed:
- **Override Taproot**: validates every input against the registered Taproot descriptor (`reviewSpend`),
  verifies change outputs by re-deriving descriptor scripts, and renders exact recipient addresses.
- **Override SegWit v0**: requires every input's full `nonWitnessUTXO` previous transaction and verifies
  `prevTx.txid == previousTxid` (preventing BIP 143 fee-inflation lies), re-derives every witness script,
  enforces `SIGHASH_ALL`, and caps fee ≤ 10% of inputs.
- **Approver**: parses the unsigned transaction, displays EVERY output address/script and amount, and
  fixes the exact `silo/approve` BIP 340 message digest over `tx.txid`. -/

namespace Tricorder.Signer

open Winnow Winnow.Keys
open Winnow.Tx (BitcoinNetwork)

/-- One output shown to the human on the LCARS Transaction Review screen. -/
structure ReviewedOutput where
  address : String
  sats : Nat
  isChange : Bool
  deriving BEq, Repr, Inhabited

/-- Verified coin metadata kept for SegWit v0 signing. -/
structure SegwitCoin where
  chain : Nat
  index : UInt32
  amount : Int64
  keys : Array ByteArray
  script : ByteArray

/-- Signing kind fixed by the review. -/
inductive ReviewKind where
  | overrideTaproot (coins : Array WalletUTXO) (tx : Transaction) (spent : Array SighashBIP341.SpentOutput)
  | overrideSegwit (coins : Array SegwitCoin) (tx : Transaction)
  | approver (tx : Transaction)

/-- Complete reviewed transaction ready for human inspection and explicit confirmation. -/
structure ReviewedTx where
  roleLabel : String
  sourceFile : String
  /-- Display txid (reversed hex, matching Bitcoin Core / explorers). -/
  txidDisplay : String
  /-- Internal txid bytes (32 bytes, committed by `silo/approve`). -/
  txidBytes : ByteArray
  inputCount : Nat
  inputTotal : Option Nat
  outputs : Array ReviewedOutput
  leaving : Option Nat
  returning : Nat
  fee : Option Nat
  psbt : PSBT
  kind : ReviewKind

def formatOutputTarget (script : ByteArray) (network : BitcoinNetwork) : String :=
  match AddressDecoder.address script network with
  | some addr => addr
  | none =>
    if script.size ≥ 1 && script[0]! == 0x6a then s!"OP_RETURN ({script.size}B)"
    else s!"SCRIPT:{hexBytes (script.extract 0 (min 20 script.size))}"

/-- `silo/approve` tagged hash matching `silo-on-winnow/Signer/Approval.lean` byte for byte. -/
def approvalMessage (txid : ByteArray) : ByteArray :=
  Secp.Sha256.tagged "silo/approve" txid

private def coordinate? (i : Identity) (found : Array (ByteArray × PSBT.KeyOrigin)) : Option (Nat × UInt32) := do
  let acct := Identity.overridePath i.network
  let (_, origin) ← found.find? fun (_, origin) =>
    origin.masterFingerprint == i.fingerprint &&
      origin.path.size == acct.size + 2 &&
      origin.path.extract 0 acct.size == acct
  let chain := origin.path[acct.size]!
  let index := origin.path[acct.size + 1]!
  if chain ≤ 1 && index < HDKey.hardenedOffset then some (chain.toNat, index) else none

private def claimedTaprootCoins (i : Identity) (psbt : PSBT) : Except String (Array WalletUTXO) := do
  let mut coins := #[]
  for h : k in [0:psbt.inputs.size] do
    let input := psbt.inputs[k]
    let some txid := input.previousTxid | throw s!"input {k + 1} missing previousTxid"
    let some vout := input.outputIndex | throw s!"input {k + 1} missing outputIndex"
    let some spent := input.witnessUTXO | throw s!"input {k + 1} missing witnessUTXO"
    let some (chain, index) := coordinate? i input.tapBIP32Derivation
      | throw s!"input {k + 1} missing this Tricorder's tapBIP32Derivation"
    coins := coins.push
      { txid, vout, amount := spent.amount, scriptPubKey := spent.scriptPubKey
        chain := if chain == 0 then .receive else .change, index, height := 0 }
  return coins

private def claimedTaprootReturns (i : Identity) (psbt : PSBT) : Array MultisigAccount.OutputCoordinate :=
  psbt.outputs.filterMap fun output =>
    (coordinate? i output.tapBIP32Derivation).map fun (chain, index) => { choice := chain, index }

def reviewOverrideTaproot (i : Identity) (account : MultisigAccount) (psbt : PSBT) (sourceFile : String) :
    Except String ReviewedTx := do
  match account.spendPath psbt with
  | .ok path => if path.isRecovery then throw "recovery-path spend is not allowed for Override signing"
  | .error e => throw s!"cannot determine spend path ({e.name})"
  let coins ← claimedTaprootCoins i psbt
  let returns := claimedTaprootReturns i psbt
  let reviewed ← match account.reviewSpend psbt coins returns 0 with
    | .ok r => pure r
    | .error (.account (.invalidSpend reason)) => throw reason
    | .error e => throw s!"PSBT review refused ({e.name})"
  if reviewed.path.isRecovery then throw "recovery-path spend refused"
  let (tx, spent) ← match psbt.unsignedTransaction, psbt.spentOutputs with
    | .ok tx, .ok spent => pure (tx, spent)
    | _, _ => throw "cannot extract unsigned transaction or spent outputs"
  let mut outputs : Array ReviewedOutput := #[]
  let mut returning : Nat := 0
  for o in reviewed.outputs do
    let sats := o.amount.toInt.toNat
    if o.isAccountOwned then returning := returning + sats
    outputs := outputs.push
      { address := formatOutputTarget o.scriptPubKey i.network, sats, isChange := o.isAccountOwned }
  let inputTotal := reviewed.inputTotal.toInt.toNat
  let fee := reviewed.fee.toInt.toNat
  return {
    roleLabel := "OVERRIDE TAPROOT (BIP340)"
    sourceFile
    txidDisplay := hexReversed tx.txid
    txidBytes := tx.txid
    inputCount := coins.size
    inputTotal := some inputTotal
    outputs
    leaving := some (inputTotal - returning)
    returning
    fee := some fee
    psbt
    kind := .overrideTaproot coins tx spent
  }

private def maxMoney : Int := 2_100_000_000_000_000

private def verifiedPrevOutput (input : PSBT.Input) (k : Nat) (txid : ByteArray) (vout : UInt32) :
    Except String Transaction.Output := do
  let some raw := (input.pair PSBT.InType.nonWitnessUTXO).map (·.value)
    | throw s!"input {k + 1} missing full nonWitnessUTXO (required for SegWit v0)"
  let prev ← match Transaction.decode raw with
    | .ok p => pure p
    | .error _ => throw s!"input {k + 1} nonWitnessUTXO failed to decode"
  unless prev.txid == txid do throw s!"input {k + 1} nonWitnessUTXO txid mismatch"
  let some out := prev.outputs[vout.toNat]? | throw s!"input {k + 1} vout out of range"
  if (input.pair PSBT.InType.witnessUTXO).isSome then
    match input.witnessUTXO with
    | some claimed =>
      unless claimed.amount == out.value && claimed.scriptPubKey == out.scriptPubKey do
        throw s!"input {k + 1} witnessUTXO disagrees with nonWitnessUTXO"
    | none => throw s!"input {k + 1} malformed witnessUTXO"
  return out

def reviewOverrideSegwit (i : Identity) (account : SegwitMultisigAccount) (psbt : PSBT) (sourceFile : String) :
    Except String ReviewedTx := do
  if psbt.inputs.isEmpty then throw "PSBT has no inputs"
  unless !psbt.outputs.isEmpty && psbt.outputs.size ≤ 1000 do throw "PSBT has invalid output count"
  unless psbt.txVersion == 1 || psbt.txVersion == 2 do throw "unsupported transaction version"
  let tx ← match psbt.unsignedTransaction with
    | .ok t => pure t
    | .error e => throw s!"cannot extract unsigned transaction ({e.name})"
  let mut coins : Array SegwitCoin := #[]
  let mut seen : Array Transaction.Outpoint := #[]
  let mut total : Int := 0
  for h : k in [0:psbt.inputs.size] do
    let input := psbt.inputs[k]
    let some txid := input.previousTxid | throw s!"input {k + 1} missing previousTxid"
    let some vout := input.outputIndex | throw s!"input {k + 1} missing outputIndex"
    if seen.contains ⟨txid, vout⟩ then throw s!"input {k + 1} duplicates an earlier outpoint"
    seen := seen.push ⟨txid, vout⟩
    let some (chain, index) := coordinate? i (PSBT.readKeyOrigins input.pairs PSBT.InType.bip32Derivation)
      | throw s!"input {k + 1} missing this Tricorder's bip32Derivation"
    let spent ← verifiedPrevOutput input k txid vout
    let there ← match SegwitMultisigAccount.resolved account chain index with
      | .ok r => pure r
      | .error e => throw s!"input {k + 1}: {e.name}"
    unless SegwitMultisigAccount.scriptPubKeyOf there.witnessScript == spent.scriptPubKey do
      throw s!"input {k + 1} script does not belong to registered descriptor"
    unless spent.value > 0 && spent.value.toInt ≤ maxMoney do throw s!"input {k + 1} invalid amount"
    unless input.sighashType.getD 1 == 1 do throw s!"input {k + 1} must use SIGHASH_ALL"
    if let some attached := input.pair PSBT.InType.witnessScript then
      unless attached.value == there.witnessScript do throw s!"input {k + 1} witnessScript mismatch"
    total := total + spent.value.toInt
    unless total ≤ maxMoney do throw "total inputs exceed max money"
    coins := coins.push { chain, index, amount := spent.value, keys := there.keys, script := there.witnessScript }
  let mut outputs : Array ReviewedOutput := #[]
  let mut paid : Int := 0
  let mut returning : Int := 0
  for h : k in [0:psbt.outputs.size] do
    let output := psbt.outputs[k]
    let some amount := output.amount | throw s!"output {k + 1} missing amount"
    let some script := output.script | throw s!"output {k + 1} missing script"
    unless amount > 0 && amount.toInt ≤ maxMoney && !script.isEmpty do
      throw s!"output {k + 1} invalid amount or script"
    paid := paid + amount.toInt
    unless paid ≤ maxMoney do throw "total outputs exceed max money"
    let mut isChange := false
    if let some (chain, index) := coordinate? i (PSBT.readKeyOrigins output.pairs PSBT.OutType.bip32Derivation) then
      if let .ok there := SegwitMultisigAccount.resolved account chain index then
        if SegwitMultisigAccount.scriptPubKeyOf there.witnessScript == script then
          isChange := true
          returning := returning + amount.toInt
    outputs := outputs.push
      { address := formatOutputTarget script i.network, sats := amount.toInt.toNat, isChange }
  unless paid ≤ total do throw "outputs exceed verified inputs"
  let fee := total - paid
  unless fee ≤ total / 10 do throw s!"fee {fee} sats exceeds 10% safety cap"
  let inputTotal := total.toNat
  let retNat := returning.toNat
  return {
    roleLabel := "OVERRIDE SEGWIT V0 (ECDSA)"
    sourceFile
    txidDisplay := hexReversed tx.txid
    txidBytes := tx.txid
    inputCount := coins.size
    inputTotal := some inputTotal
    outputs
    leaving := some (inputTotal - retNat)
    returning := retNat
    fee := some fee.toNat
    psbt
    kind := .overrideSegwit coins tx
  }

/-- Reviews a PSBT for Override Key signing against the registered wallet descriptor. -/
def reviewOverride (i : Identity) (w : RegisteredWallet) (psbt : PSBT) (sourceFile : String) :
    Except String ReviewedTx :=
  match w.account with
  | .taproot account => reviewOverrideTaproot i account psbt sourceFile
  | .segwit account => reviewOverrideSegwit i account psbt sourceFile

/-- Reviews a PSBT for Silo Approver signing (`silo/approve` over `tx.txid`).
If a wallet descriptor is also registered, marks verified change outputs so the approver can distinguish
change from external recipients. -/
def reviewApprover (i : Identity) (wallet? : Option RegisteredWallet) (psbt : PSBT) (sourceFile : String) :
    Except String ReviewedTx := do
  let tx ← match psbt.unsignedTransaction with
    | .ok t => pure t
    | .error e => throw s!"cannot extract unsigned transaction ({e.name})"
  if tx.inputs.isEmpty then throw "transaction has no inputs"
  if tx.outputs.isEmpty then throw "transaction has no outputs"
  let mut outputs : Array ReviewedOutput := #[]
  let mut returning : Nat := 0
  let mut outSum : Nat := 0
  for h : k in [0:tx.outputs.size] do
    let out := tx.outputs[k]
    let sats := out.value.toInt.toNat
    outSum := outSum + sats
    let mut isChange := false
    if let some w := wallet? then
      if h2 : k < psbt.outputs.size then
        let po := psbt.outputs[k]
        match w.account with
        | .taproot acc =>
          if let some (chain, idx) := coordinate? i po.tapBIP32Derivation then
            if let .ok addr := acc.address idx chain then
              if AddressDecoder.address out.scriptPubKey i.network == some addr then
                isChange := true
        | .segwit acc =>
          if let some (chain, idx) := coordinate? i (PSBT.readKeyOrigins po.pairs PSBT.OutType.bip32Derivation) then
            if let .ok there := SegwitMultisigAccount.resolved acc chain idx then
              if SegwitMultisigAccount.scriptPubKeyOf there.witnessScript == out.scriptPubKey then
                isChange := true
    if isChange then returning := returning + sats
    outputs := outputs.push
      { address := formatOutputTarget out.scriptPubKey i.network, sats, isChange }
  -- Compute input total / fee if every input carries witnessUTXO.
  let mut knownInputs : Option Nat := some 0
  for input in psbt.inputs do
    match knownInputs, input.witnessUTXO with
    | some acc, some u => knownInputs := some (acc + u.amount.toInt.toNat)
    | _, _ => knownInputs := none
  let fee := knownInputs.bind fun tot => if tot ≥ outSum then some (tot - outSum) else none
  let leaving := knownInputs.map fun tot => tot - returning
  return {
    roleLabel := "SILO APPROVER (BIP340)"
    sourceFile
    txidDisplay := hexReversed tx.txid
    txidBytes := tx.txid
    inputCount := tx.inputs.size
    inputTotal := knownInputs
    outputs
    leaving
    returning
    fee
    psbt
    kind := .approver tx
  }

/-- Parses either raw binary PSBT (`psbt\xff`) or Base64 PSBT text. -/
def parsePsbtBytes (bytes : ByteArray) : Except String PSBT := do
  if bytes.size ≥ 5 && bytes[0]! == 0x70 && bytes[1]! == 0x73 && bytes[2]! == 0x62 && bytes[3]! == 0x74 && bytes[4]! == 0xff then
    match PSBT.parse bytes with
    | .ok p => pure p
    | .error e => throw s!"binary PSBT decode failed ({e.name})"
  else
    let some text := String.fromUTF8? bytes | throw "PSBT file is neither raw PSBT nor UTF-8 Base64"
    match PSBT.ofBase64 text.trimAscii.toString with
    | .ok p => pure p
    | .error e => throw s!"base64 PSBT decode failed ({e.name})"

end Tricorder.Signer
