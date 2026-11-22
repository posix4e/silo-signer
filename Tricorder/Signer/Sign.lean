import WinnowCore
import Winnow.Wallet.PSBTRoles
import SecpCt.Schnorr
import SecpCt.Ecdsa
import Secp.Der
import Tricorder.Crypto.Key
import Tricorder.Signer.Review

/-! # Constant-time PSBT signing (`SecpCt`)

Every signature is produced by `SecpCt` on machine words and immediately verified against the public key
before leaving Tricorder. -/

namespace Tricorder.Signer

open Winnow Winnow.Keys

/-- Artifact produced after explicit human confirmation on a `ReviewedTx`. -/
structure SignedResult where
  roleLabel : String
  txidDisplay : String
  outFileName : String
  /-- Text payload written to `outbox/` and encoded as QR: the signed PSBT in base64. -/
  payloadText : String
  /-- Short human-readable summary for the LCARS Signed screen. -/
  summary : String
  deriving BEq, Repr, Inhabited

private def signTaprootInput (i : Identity) (psbt : PSBT) (k : Nat) (coin : WalletUTXO) (tx : Transaction)
    (spent : Array SighashBIP341.SpentOutput) (fresh : ByteArray) : Except String PSBT := do
  let some key := (i.overrideSecret.child coin.chain.rawValue.toUInt32).bind (·.child coin.index)
    | throw s!"cannot derive override key for input {k + 1}"
  let (_, leaves, hashType) ← match psbt.leafSigningContexts k with
    | .ok found => pure found
    | .error _ => throw s!"input {k + 1} missing leaf signing context"
  let mut sigs := psbt.inputs[k]!.tapScriptSignatures
  let mut made := 0
  for (leaf, policy) in leaves do
    if policy.relativeLock.isSome || !policy.keys.contains key.xonly then continue
    let path := SighashBIP341.ScriptPath.ofLeaf ⟨leaf.script⟩ leaf.leafVersion
    let digest ← match SighashBIP341.sighash tx k spent hashType (some path) with
      | .ok d => pure d
      | .error _ => throw s!"BIP341 sighash failed for input {k + 1}"
    let some sig := SecpCt.sign key.key digest fresh | throw s!"BIP340 sign failed for input {k + 1}"
    unless SecpCt.verify sig digest key.xonly do
      throw s!"self-verify failed for Taproot input {k + 1}"
    let item := if hashType.rawValue != 0 then sig.push hashType.rawValue else sig
    let id : PSBT.TapScriptSignatureID := { publicKey := key.xonly, leafHash := leaf.leafHash }
    sigs := match sigs.findIdx? (fun (o, _) => o.publicKey == id.publicKey && o.leafHash == id.leafHash) with
      | some j => sigs.set! j (id, item)
      | none => sigs.push (id, item)
    made := made + 1
  if made == 0 then throw s!"input {k + 1} has no immediate leaf containing our Override key"
  return { psbt with inputs := psbt.inputs.modify k (·.setTapScriptSignatures sigs) }

private def signSegwitInput (i : Identity) (psbt : PSBT) (k : Nat) (coin : SegwitCoin) (tx : Transaction)
    (fresh : ByteArray) : Except String PSBT := do
  let some key := (i.overrideSecret.child coin.chain.toUInt32).bind (·.child coin.index)
    | throw s!"cannot derive override key for input {k + 1}"
  unless coin.keys.contains key.publicKey do
    throw s!"input {k + 1} does not contain our Override key"
  let some digest := SighashBIP143.sighashAll tx k coin.script coin.amount
    | throw s!"BIP143 sighash failed for input {k + 1}"
  let some sig := SecpCt.Ecdsa.sign key.key digest fresh | throw s!"ECDSA sign failed for input {k + 1}"
  unless SecpCt.Ecdsa.verify sig digest key.publicKey do
    throw s!"self-verify failed for SegWit input {k + 1}"
  let item := (Secp.Ecdsa.der sig).push 0x01
  let ws := PSBT.KeyValue.make PSBT.InType.witnessScript .empty coin.script
  let ps := PSBT.KeyValue.make PSBT.InType.partialSignature key.publicKey item
  return { psbt with inputs := psbt.inputs.modify k fun input => (input.set ws).set ps }

/-- Signs a `ReviewedTx` using `fresh` (32 random bytes from OS CSPRNG).
Every signature is verified before returning. -/
def signReviewed (i : Identity) (reviewed : ReviewedTx) (fresh : ByteArray) : Except String SignedResult := do
  unless fresh.size == 32 do throw "signing requires 32 fresh random bytes"
  match reviewed.kind with
  | .overrideTaproot coins tx spent =>
    let mut signed := reviewed.psbt
    for h : k in [0:coins.size] do
      let inputFresh := sha256 (fresh ++ u32BE k.toUInt32)
      signed ← signTaprootInput i signed k coins[k] tx spent inputFresh
    let b64 := signed.base64
    return {
      roleLabel := reviewed.roleLabel
      txidDisplay := reviewed.txidDisplay
      outFileName := "outbox/signed.psbt.b64"
      payloadText := b64
      summary := s!"SIGNED {coins.size} TAPROOT INPUT(S)"
    }
  | .overrideSegwit coins tx =>
    let mut signed := reviewed.psbt
    for h : k in [0:coins.size] do
      let inputFresh := sha256 (fresh ++ u32BE k.toUInt32)
      signed ← signSegwitInput i signed k coins[k] tx inputFresh
    let b64 := signed.base64
    return {
      roleLabel := reviewed.roleLabel
      txidDisplay := reviewed.txidDisplay
      outFileName := "outbox/signed.psbt.b64"
      payloadText := b64
      summary := s!"SIGNED {coins.size} SEGWIT V0 INPUT(S)"
    }

end Tricorder.Signer
