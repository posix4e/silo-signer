import WinnowCore
import Tricorder.Crypto.Key

/-! # Registered wallet descriptors (Taproot `sortedmulti_a` and SegWit v0 `sortedmulti`)

Tricorder's Override Key signs only for a wallet descriptor that:
1. Parses strictly for this build's Bitcoin network (valid checksum if present);
2. Contains this device's Override extended public key;
3. Requires at least 2 distinct keys (`threshold ≥ 2`, no duplicate key).

Supports both wallet kinds Silo serves:
- Taproot: `tr(nobody, sortedmulti_a(k, KEY, …))` (BIP 340)
- SegWit v0: `wsh(sortedmulti(k, KEY, …))` (ECDSA) -/

namespace Tricorder.Signer

open Winnow Winnow.Keys
open Winnow.Tx (BitcoinNetwork)

inductive RegisteredAccount where
  | taproot (account : MultisigAccount)
  | segwit (account : SegwitMultisigAccount)

structure RegisteredWallet where
  account : RegisteredAccount
  descriptor : String
  firstAddress : String
  kindLabel : String
  threshold : Nat
  keyCount : Nat

private def isOurKey (i : Identity) (key : Descriptor.SingleKey) : Bool :=
  match MultisigAccount.extendedKey? key with
  | some (base, _) =>
    base.publicKey == i.overrideAccount.publicKey && base.chainCode == i.overrideAccount.chainCode
  | none => false

private def sameTaprootKey (a b : Descriptor.SingleKey) : Bool :=
  match MultisigAccount.extendedKey? a, MultisigAccount.extendedKey? b with
  | some (x, _), some (y, _) => x.publicKey == y.publicKey
  | _, _ => true

private def distinctTaproot (keys : Array Descriptor.SingleKey) : Bool :=
  (List.range keys.size).all fun a => (List.range a).all fun b => !sameTaprootKey keys[a]! keys[b]!

private def segwitBody (text : String) : Except String (Array Char) :=
  let cs := text.trimAscii.toString.toList.toArray
  match (cs.toList.zipIdx.filter (·.1 == '#')).getLast?.map (·.2) with
  | none => .ok cs
  | some mark =>
    let checksum := cs.extract (mark + 1) cs.size
    let body := cs.extract 0 mark
    if checksum.size == 8 && Descriptor.Checksum.verify (String.ofList body.toList) (String.ofList checksum.toList) then
      .ok body
    else .error "descriptor checksum is invalid"

private def whyMultisig : MultisigFailure → String
  | .account (.invalidDescriptor reason) => reason
  | .account (.invalidSpend reason) => reason
  | failure => failure.name

def parseSegwit (text : String) (network : BitcoinNetwork) : Except String SegwitMultisigAccount := do
  let cs ← segwitBody text
  let (threshold, keys) ← match SegwitMultisigAccount.parseExpression.run ⟨cs, 0⟩ with
    | .ok (args, rest) =>
      if rest.i == rest.cs.size then pure args else throw "trailing characters after descriptor"
    | .error e => throw s!"invalid wsh(sortedmulti(...)) descriptor ({e.name})"
  unless keys.size ≤ SegwitMultisigAccount.maxKeys do
    throw s!"descriptor has more than {SegwitMultisigAccount.maxKeys} keys"
  for key in keys do
    match SegwitMultisigAccount.requireKey key network with
    | .ok () => pure ()
    | .error refusal => throw (whyMultisig refusal)
  return { network, threshold := threshold.toNat, keys }

def registerTaproot (i : Identity) (text : String) : Except String RegisteredWallet := do
  let trimmed := text.trimAscii.toString
  let account ← match MultisigAccount.parse trimmed i.network with
    | .ok a => pure a
    | .error e => throw s!"invalid Taproot descriptor ({e.name})"
  if account.signersLeaves.isEmpty then throw "descriptor has no immediate-spend leaf"
  unless account.signersLeaves.any (·.keys.any (isOurKey i)) do
    throw "descriptor does not contain this signer's override key"
  unless account.signersLeaves.all (fun leaf => leaf.threshold.toNat ≥ 2 && distinctTaproot leaf.keys) do
    throw "descriptor allows single-key spend or repeats a key"
  let first ← match account.address 0 0 with
    | .ok addr => pure addr
    | .error e => throw s!"cannot derive receive address 0 ({e.name})"
  let leaf0 := account.signersLeaves[0]!
  return {
    account := .taproot account
    descriptor := account.descriptor.serialized
    firstAddress := first
    kindLabel := s!"TAPROOT {leaf0.threshold.toNat}-OF-{leaf0.keys.size}"
    threshold := leaf0.threshold.toNat
    keyCount := leaf0.keys.size
  }

def registerSegwit (i : Identity) (text : String) : Except String RegisteredWallet := do
  let account ← parseSegwit text i.network
  unless account.keys.any (isOurKey i) do
    throw "descriptor does not contain this signer's override key"
  unless account.threshold ≥ 2 && SegwitMultisigAccount.allDifferent (account.keys.map SegwitMultisigAccount.identity) do
    throw "descriptor allows single-key spend or repeats a key"
  let first ← match SegwitMultisigAccount.resolved account 0 0 with
    | .ok there => pure there.output.address
    | .error e => throw (whyMultisig e)
  return {
    account := .segwit account
    descriptor := SegwitMultisigAccount.serialized account
    firstAddress := first
    kindLabel := s!"SEGWIT V0 {account.threshold}-OF-{account.keys.size}"
    threshold := account.threshold
    keyCount := account.keys.size
  }

/-- Validates and registers either a `wsh(sortedmulti(...))` or `tr(..., sortedmulti_a(...))` descriptor. -/
def registerDescriptor (i : Identity) (text : String) : Except String RegisteredWallet :=
  let t := text.trimAscii.toString
  if t.startsWith "wsh(" then registerSegwit i t else registerTaproot i t

end Tricorder.Signer
