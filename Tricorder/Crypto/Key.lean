import Winnow.Keys.BIP32
import Winnow.Tx
import SecpCt.Schnorr
import SecpCt.Keys
import Tricorder.Crypto.Bip39Ascii

/-! # Constant-time key derivation (`SecpCt`) for Override and Approver roles

All secret-key arithmetic runs exclusively through `SecpCt` on machine words (never Lean `Nat`).
From one 24-word BIP39 seed:
- **Override Key** (BIP32 Taproot / SegWit multisig account): `m/86'/coin'/0'`
- **Approver Key** (Silo `silo/approve` BIP340 x-only key):   `m/86'/coin'/1'/0/0`

The two accounts use disjoint hardened indices (`0'` vs `1'`), so compromise of one child chain never
derives the other. -/

namespace Tricorder

open Winnow Winnow.Keys
open Winnow.Tx (BitcoinNetwork)

/-- A BIP32 secret key + chain code + compressed public key (33 bytes). -/
structure SecretKey where
  key : ByteArray
  chain : ByteArray
  publicKey : ByteArray

def compressedKey (secret : ByteArray) : Option ByteArray :=
  (SecpCt.publicKey secret).map fun (x, odd) => ByteArray.mk #[if odd == 1 then 3 else 2] ++ x

namespace SecretKey

def ofSeed (seed : ByteArray) : Option SecretKey :=
  let i := hmacSha512 "Bitcoin seed".toUTF8 seed
  let key := i.extract 0 32
  (compressedKey key).map fun publicKey => { key, chain := i.extract 32 64, publicKey }

def child (s : SecretKey) (index : UInt32) : Option SecretKey := do
  let data := if index ≥ HDKey.hardenedOffset then ByteArray.mk #[0] ++ s.key else s.publicKey
  let i := hmacSha512 s.chain (data ++ u32BE index)
  let tweak := i.extract 0 32
  if SecpCt.Sc.isBelowN tweak == 0 then none
  let key ← SecpCt.addKeys s.key tweak
  let publicKey ← compressedKey key
  return { key, chain := i.extract 32 64, publicKey }

def derivePath (s : SecretKey) (path : Array UInt32) : Option SecretKey :=
  path.foldlM child s

def fingerprint (s : SecretKey) : UInt32 :=
  (readBE (hash160 s.publicKey) 0 4).toUInt32

def xonly (s : SecretKey) : ByteArray :=
  s.publicKey.extract 1 33

end SecretKey

def hexBytes (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList [Nat.digitChar (x.toNat / 16), Nat.digitChar (x.toNat % 16)]) ""

def hexReversed (b : ByteArray) : String :=
  let rev := ByteArray.mk b.data.reverse
  hexBytes rev

def hex8 (n : UInt32) : String :=
  String.ofList ((List.range 8).map fun i => Nat.digitChar ((n.toNat >>> (4 * (7 - i))) % 16))

def unhex? (text : String) : Option ByteArray := do
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
    else none
  let rec go : List Char → ByteArray → Option ByteArray
    | [], out => some out
    | hi :: lo :: rest, out => do go rest (out.push ((← digit hi) * 16 + (← digit lo)).toUInt8)
    | [_], _ => none
  go text.trimAscii.toString.toList ByteArray.empty

/-- Unlocked signer identity holding both the Override account secret and the Approver key secret.
Dropped immediately when Tricorder locks or pauses (`Mini/Alloc` zeroes freed blocks). -/
structure Identity where
  network : BitcoinNetwork
  fingerprint : UInt32
  /-- Public extended key at `m/86'/coin'/0'` for descriptor expressions. -/
  overrideAccount : HDKey
  /-- Secret extended key at `m/86'/coin'/0'`. -/
  overrideSecret : SecretKey
  /-- Dedicated Silo Approver key at `m/86'/coin'/1'/0/0`. -/
  approverSecret : SecretKey

namespace Identity

def hardened (n : UInt32) : UInt32 := n + HDKey.hardenedOffset

def coinIndex (network : BitcoinNetwork) : UInt32 :=
  if network == .mainnet then 0 else 1

def overridePath (network : BitcoinNetwork) : Array UInt32 :=
  #[hardened 86, hardened (coinIndex network), hardened 0]

def approverPath (network : BitcoinNetwork) : Array UInt32 :=
  #[hardened 86, hardened (coinIndex network), hardened 1, 0, 0]

def keyNetwork (network : BitcoinNetwork) : HDKey.Network :=
  if network == .mainnet then .mainnet else .testnet

/-- Derives both Override and Approver keys from a BIP32 seed (64 bytes from BIP39, or 32 bytes in tests). -/
def ofSeed (seed : ByteArray) (network : BitcoinNetwork) : Except String Identity := do
  unless seed.size ≥ 16 && seed.size ≤ 64 do throw "seed must be 16..64 bytes"
  let derived : Option Identity := do
    let root ← SecretKey.ofSeed seed
    let purpose ← root.child (hardened 86)
    let coin ← purpose.child (hardened (coinIndex network))
    let overrideSecret ← coin.child (hardened 0)
    let overrideAccount : HDKey :=
      { depth := 3
        parentFingerprint := coin.fingerprint
        childIndex := hardened 0
        chainCode := overrideSecret.chain
        privateKey := none
        publicKey := overrideSecret.publicKey }
    let approverAcct ← coin.child (hardened 1)
    let approverBranch ← approverAcct.child 0
    let approverSecret ← approverBranch.child 0
    return { network, fingerprint := root.fingerprint, overrideAccount, overrideSecret, approverSecret }
  match derived with
  | some id => return id
  | none => throw "seed failed BIP32 key derivation"

def ofWords (words : Array String) (network : BitcoinNetwork) : Except String Identity := do
  let _ ← Bip39Ascii.validate words
  ofSeed (Bip39Ascii.toSeed words) network

/-- Descriptor key expression for the Override key: `[fp/86h/coin h/0h]xpub...`. -/
def overrideKeyExpression (i : Identity) : String :=
  s!"[{hex8 i.fingerprint}/86h/{coinIndex i.network}h/0h]{i.overrideAccount.serialized (keyNetwork i.network)}"

/-- 32-byte x-only public key (hex) for registering Tricorder as a Silo Approver. -/
def approverPubKeyHex (i : Identity) : String :=
  hexBytes i.approverSecret.xonly

def fingerprintHex (i : Identity) : String :=
  hex8 i.fingerprint

end Identity

end Tricorder
