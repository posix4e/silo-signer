import Platform
import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign

/-! # Headless CLI for Bitcoin Core regtest co-signing tests (`scripts/regtest-e2e`)

Exercises the exact same `Tricorder.Signer` code compiled on the minimal runtime against real
`bitcoind` wallets for both Taproot (`tr(..., sortedmulti_a(2, ...))`) and SegWit v0
(`wsh(sortedmulti(2, ...))`) 2-of-3 co-signing plus Silo `silo/approve` verification. -/

open Tricorder Tricorder.Signer Winnow Winnow.Keys

private def println (s : String) : IO Unit := Platform.write (s ++ "\n").toUTF8

private def loadIdentity (seedHex : String) (net : Network) : Except String Identity := do
  let some ent := unhex? seedHex | throw "invalid seed hex"
  let words ← Bip39Ascii.fromEntropy ent
  Identity.ofWords words net.toBitcoin

def main (args : List String) : IO UInt32 := do
  match args with
  | ["keys", netStr, seedHex] =>
    let some net := Network.parse? netStr | do println "error: bad network"; return 2
    match loadIdentity seedHex net with
    | .error e => println s!"error: {e}"; return 1
    | .ok id =>
      println id.overrideKeyExpression
      println id.approverPubKeyHex
      println id.fingerprintHex
      return 0
  | ["addr0", netStr, seedHex, desc] =>
    let some net := Network.parse? netStr | do println "error: bad network"; return 2
    match loadIdentity seedHex net >>= fun id => registerDescriptor id desc with
    | .error e => println s!"error: {e}"; return 1
    | .ok w => println w.firstAddress; return 0
  | ["sign-override", netStr, seedHex, desc, psbtB64] =>
    let some net := Network.parse? netStr | do println "error: bad network"; return 2
    let fresh ← Platform.random 32
    let res : Except String SignedResult := do
      let id ← loadIdentity seedHex net
      let w ← registerDescriptor id desc
      let psbt ← parsePsbtBytes psbtB64.toUTF8
      let rev ← reviewOverride id w psbt "cli.psbt"
      signReviewed id rev fresh
    match res with
    | .error e => println s!"error: {e}"; return 1
    | .ok signed => println signed.payloadText; return 0
  | ["sign-approve", netStr, seedHex, psbtB64] =>
    let some net := Network.parse? netStr | do println "error: bad network"; return 2
    let fresh ← Platform.random 32
    let res : Except String SignedResult := do
      let id ← loadIdentity seedHex net
      let psbt ← parsePsbtBytes psbtB64.toUTF8
      let rev ← reviewApprover id none psbt "approve.psbt"
      signReviewed id rev fresh
    match res with
    | .error e => println s!"error: {e}"; return 1
    | .ok signed => println signed.payloadText; return 0
  | _ =>
    println "usage: regtest-cli keys|addr0|sign-override|sign-approve ..."
    return 2
