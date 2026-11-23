import Platform
import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Tricorder.Crypto.Vault
import Tricorder.Crypto.Key
import Tricorder.Signer.Descriptor
import Tricorder.Signer.Review
import Tricorder.Signer.Sign
import Tests.Fixture
import Tricorder.Ui.Layout
import Tricorder.Signer.Protocol
import Tricorder.Qr.Encode

/-! # Pure tests for the crypto, the vault, the override key's review and signing, and the QR encoder -/

open Tricorder Tricorder.Signer Winnow Winnow.Keys

private def println (s : String) : IO Unit := Platform.write (s ++ "\n").toUTF8

private def check (fails : IO.Ref Nat) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  if ok then
    println s!"ok    {name}"
  else
    println s!"FAIL  {name}{if detail.isEmpty then "" else ": " ++ detail}"
    fails.modify (· + 1)

def main : IO UInt32 := do
  let fails ← IO.mkRef 0

  -- 1. BIP39 24-word official test vector (all-zero 256-bit entropy -> "abandon ... art")
  let zero32 := ByteArray.mk (Array.replicate 32 0)
  match Bip39Ascii.fromEntropy zero32 with
  | .error e => check fails "BIP39 all-zero 24 words" false e
  | .ok words =>
    let expected := "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon art"
    check fails "BIP39 all-zero 24-word vector matches spec" (Bip39Ascii.joinWords words == expected)
    check fails "BIP39 validate round-trip" ((Bip39Ascii.validate words).toOption == some zero32)
    let bad := words.set! 23 "abandon"
    check fails "BIP39 rejects bad checksum" (!(Bip39Ascii.validate bad).isOk)
    let seed := Bip39Ascii.toSeed words
    check fails "BIP39 PBKDF2 seed matches standard vector"
      (hexBytes (seed.extract 0 8) == "408b285c12383600") (hexBytes (seed.extract 0 8))

  -- 2. Vault seal / open / wrong PIN / wrong network
  -- 1b. Twelve words: BIP39's own vectors, and BIP86's key for the first of them.
  let twelve := Bip39Ascii.splitSentence "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about"
  check fails "BIP39 12 words: all-zero 128-bit entropy" ((Bip39Ascii.validate twelve).toOption == some (ByteArray.mk (Array.replicate 16 0)))
  check fails "BIP39 12 words: bad checksum refused" (!(Bip39Ascii.validate (twelve.set! 11 "abandon")).isOk)
  let legal := Bip39Ascii.splitSentence "legal winner thank year wave sausage worth useful legal winner thank yellow"
  check fails "BIP39 12 words: 7f.. entropy" ((Bip39Ascii.validate legal).toOption == some (ByteArray.mk (Array.replicate 16 0x7f)))
  check fails "BIP39 refuses 13 words" (!(Bip39Ascii.validate (twelve.push "about")).isOk)
  check fails "BIP39 refuses 15 words" (!(Bip39Ascii.validate (twelve ++ #["abandon", "abandon", "about"])).isOk)
  check fails "BIP39 12 words: the seed of the specification" (hexBytes (Bip39Ascii.toSeed twelve) ==
    "5eb00bbddcf069084889a8ab9155568165f5c453ccb85e70811aaed6f6da5fc19a5ac40b389cd370d086206dec8aa6c43daea6690f20ad3d8d48b2d2ce9e38e4")
  match Identity.ofWords twelve .mainnet with
  | .error e => check fails "12 words make an identity" false e
  | .ok id12 =>
    check fails "12 words: BIP86's account key at m/86'/0'/0'" (id12.overrideKeyExpression.endsWith
      "xpub6BgBgsespWvERF3LHQu6CnqdvfEvtMcQjYrcRzx53QJjSxarj2afYWcLteoGVky7D3UKDP9QyrLprQ3VCECoY49yfdDEHGCtMMj92pReUsQ")
  let .ok words := Bip39Ascii.fromEntropy zero32 | do println "FAIL words"; return 1
  let salt := ByteArray.mk ((Array.range 16).map (·.toUInt8))
  let nonce := ByteArray.mk ((Array.range 12).map (fun i => (i + 7).toUInt8))
  match Vault.sealVault .signet "170147" words salt nonce 10 with
  | .error e => check fails "Vault seal" false e
  | .ok blob =>
    check fails "Vault opens with right PIN and network" ((Vault.openVault .signet "170147" blob).toOption == some words)
    check fails "Vault refuses wrong PIN" (!(Vault.openVault .signet "170148" blob).isOk)
    check fails "Vault refuses wrong network" (!(Vault.openVault .mainnet "170147" blob).isOk)
    let tampered := blob.set! (blob.size - 1) (blob[blob.size - 1]! ^^^ 1)
    check fails "Vault refuses tampered GCM tag" (!(Vault.openVault .signet "170147" tampered).isOk)
    check fails "Vault rejects short PIN (< 6)" (!(Vault.sealVault .signet "12345" words salt nonce 10).isOk)

  -- 3. Identity derivation
  let .ok idA := Identity.ofWords words .regtest | do println "FAIL idA"; return 1
  let entB := ByteArray.mk ((Array.range 32).map (fun i => (i + 1).toUInt8))
  let entC := ByteArray.mk ((Array.range 32).map (fun i => (i + 99).toUInt8))
  let .ok wordsB := Bip39Ascii.fromEntropy entB | do println "FAIL wordsB"; return 1
  let .ok wordsC := Bip39Ascii.fromEntropy entC | do println "FAIL wordsC"; return 1
  let .ok idB := Identity.ofWords wordsB .regtest | do println "FAIL idB"; return 1
  let .ok idC := Identity.ofWords wordsC .regtest | do println "FAIL idC"; return 1
  check fails "Override key expression has origin & tpub"
    (idA.overrideKeyExpression.startsWith s!"[{idA.fingerprintHex}/86h/1h/0h]tpub")
    idA.overrideKeyExpression

  -- 4. Descriptor registration (Taproot 2-of-3 & SegWit v0 2-of-3)
  let trBody := s!"tr(50929b74c1a04954b78b4b6035e97a5e078a5a0f28ec96d547bfee9ace803ac0,sortedmulti_a(2,{idA.overrideKeyExpression}/<0;1>/*,{idB.overrideKeyExpression}/<0;1>/*,{idC.overrideKeyExpression}/<0;1>/*))"
  let mut trAddr := ""
  match registerDescriptor idA trBody with
  | .error e => check fails "Register Taproot 2-of-3 descriptor" false e
  | .ok w =>
    trAddr := w.firstAddress
    check fails "Taproot descriptor registers with bcrt1p address"
      (w.firstAddress.startsWith "bcrt1p" && w.threshold == 2 && w.keyCount == 3)
      w.firstAddress
  let swBody := s!"wsh(sortedmulti(2,{idA.overrideKeyExpression}/<0;1>/*,{idB.overrideKeyExpression}/<0;1>/*,{idC.overrideKeyExpression}/<0;1>/*))"
  match registerDescriptor idA swBody with
  | .error e => check fails "Register SegWit v0 2-of-3 descriptor" false e
  | .ok w =>
    check fails "SegWit v0 descriptor registers with bcrt1q address"
      (w.firstAddress.startsWith "bcrt1q" && w.threshold == 2 && w.keyCount == 3)
      w.firstAddress
  let foreignBody := s!"wsh(sortedmulti(2,{idB.overrideKeyExpression}/<0;1>/*,{idC.overrideKeyExpression}/<0;1>/*))"
  check fails "Refuses descriptor without our Override key" (!(registerDescriptor idA foreignBody).isOk)

  -- 5. The override key's review of a payment, and its signature
  match Tests.Fixture.overridePayment idA idB idC 5 190000 with
  | .error e => check fails "A payment of five outputs is made for the tests" false e
  | .ok (wallet, psbt, _) =>
    match reviewOverride idA wallet psbt "payment.psbt" with
    | .error e => check fails "Override review" false e
    | .ok rev =>
      check fails "The review has every output, none of them the wallet's own by its say-so"
        (rev.outputs.size == 5 && rev.outputs.all (fun o => o.sats == 190000 && !o.isChange))
      check fails "What leaves is the inputs less nothing, and the fee is the rest"
        (rev.leaving == some 1000000 && rev.fee == some 50000)
      check fails "Five outputs are two pages of three, and only the second is the last"
        (rev.pageCount == 2 && !rev.isLastPage 0 && rev.isLastPage 1)
      check fails "Every address fits whole in three lines of 30"
        (rev.outputs.all fun o => o.address.length ≤ 90 &&
          String.ofList (Tricorder.Ui.wrapChars 30 3 o.address.toList).flatten == o.address)
      let fresh := ByteArray.mk ((Array.range 32).map (fun i => (i * 13 + 5).toUInt8))
      match signReviewed idA rev fresh with
      | .error e => check fails "Override sign" false e
      | .ok res =>
        let signedOk := match PSBT.ofBase64 res.payloadText with
          | .ok signed => (signed.inputs[0]?.map fun i => i.partialSignatures.size == 1).getD false
          | .error _ => false
        check fails "The signed payment carries the override key's signature" signedOk
    -- A fee over a tenth of the inputs is refused
    match Tests.Fixture.overridePayment idA idB idC 1 800000 with
    | .ok (w2, greedy, _) =>
      check fails "A payment whose fee is over a tenth of its inputs is refused" (!(reviewOverride idA w2 greedy "greedy.psbt").isOk)
    | .error e => check fails "A greedy payment is made for the tests" false e
    -- Another signer's wallet does not review it
    check fails "A signer whose key is not at the claimed place refuses the payment"
      (match registerDescriptor idB (Tests.Fixture.descriptor idA idB idC) with
       | .ok wB => !(reviewOverride idB wB psbt "payment.psbt").isOk
       | .error _ => false)

  -- 6. Pure-Lean QR encoder across small (v1), medium (override key), and large (PSBT-size) payloads
  let q1 := Qr.encode "TRICORDER"
  let q2 := Qr.encode idA.overrideKeyExpression
  let q3 := Qr.encode (String.ofList (List.replicate 420 'A'))
  check fails "QR encodes short payload (v1, 21x21)" (match q1 with | some q => q.version == 1 && q.size == 21 | none => false)
  check fails "QR encodes override key expression" (q2.isSome)
  check fails "QR encodes 420-byte multi-block payload" (match q3 with | some q => q.version ≥ 13 && q.modules.size == q.size * q.size | none => false)

  let n ← fails.get
  if n == 0 then
    println "signer-test: all checks passed"
    return 0
  else
    println s!"signer-test: {n} failed"
    return 1
