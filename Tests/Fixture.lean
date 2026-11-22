import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review

/-! # A payment for the tests to review and sign

A SegWit v0 wallet of two of three keys, one coin in it, and a PSBT that spends the coin to as many outputs as
asked for, with everything the override key's review requires: the whole previous transaction, the witness
script, and where in the wallet the signer's key is. -/

namespace Tests.Fixture

open Tricorder Tricorder.Signer Winnow Winnow.Keys

def descriptor (a b c : Identity) : String :=
  s!"wsh(sortedmulti(2,{a.overrideKeyExpression}/<0;1>/*,{b.overrideKeyExpression}/<0;1>/*,{c.overrideKeyExpression}/<0;1>/*))"

/-- The wallet as `a` registers it, a PSBT spending its one coin of 1,000,000 sats to `outputs` outputs of
`each` sats, and the transaction the PSBT is of. The outputs pay the wallet's own later addresses, but say
nothing of that, so the review must call them payments to someone else. -/
def overridePayment (a b c : Identity) (outputs : Nat) (each : Int64) :
    Except String (RegisteredWallet × PSBT × Transaction) := do
  let wallet ← registerDescriptor a (descriptor a b c)
  let .segwit account := wallet.account | throw "fixture: not a SegWit v0 wallet"
  let at' (index : UInt32) : Except String SegwitMultisigAccount.Resolved :=
    match SegwitMultisigAccount.resolved account 0 index with
    | .ok there => pure there
    | .error e => throw s!"fixture: {e.name}"
  let coin ← at' 0
  let zero32 := ByteArray.mk (Array.replicate 32 0)
  let previous : Transaction :=
    { version := 2
      inputs := #[{ previousOutput := ⟨zero32, 0⟩, scriptSig := .empty, sequence := 0xffffffff }]
      outputs := #[{ value := 1000000, scriptPubKey := SegwitMultisigAccount.scriptPubKeyOf coin.witnessScript }]
      locktime := 0 }
  let mut paid : Array Transaction.Output := #[]
  for k in [0:outputs] do
    let there ← at' (k + 1).toUInt32
    paid := paid.push { value := each, scriptPubKey := SegwitMultisigAccount.scriptPubKeyOf there.witnessScript }
  let tx : Transaction :=
    { version := 2
      inputs := #[{ previousOutput := ⟨previous.txid, 0⟩, scriptSig := .empty, sequence := 0xfffffffd }]
      outputs := paid
      locktime := 0 }
  let some ours := (a.overrideSecret.child 0).bind (·.child 0) | throw "fixture: cannot derive the key"
  let origin : PSBT.KeyOrigin :=
    { masterFingerprint := a.fingerprint, path := Identity.overridePath a.network ++ #[0, 0] }
  let pairs := PSBT.writeKeyOrigins
    #[PSBT.KeyValue.make PSBT.InType.nonWitnessUTXO .empty (previous.serialized false),
      PSBT.KeyValue.make PSBT.InType.witnessScript .empty coin.witnessScript]
    PSBT.InType.bip32Derivation #[(ours.publicKey, origin)]
  match PSBT.ofV0 tx #[] #[{ pairs }] (paid.map fun _ => { pairs := #[] }) with
  | .ok psbt => return (wallet, psbt, tx)
  | .error _ => throw "fixture: the PSBT would not be made"

end Tests.Fixture
