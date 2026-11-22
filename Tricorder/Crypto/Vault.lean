import Winnow.Crypto
import Tricorder.Network
import Tricorder.Crypto.Bip39Ascii
import Secret

/-! # Encrypted key vault (`vault.bin`) and wrong-PIN auto-wipe policy

Format of `vault.bin`:
  - bytes `0..6`   : ASCII magic `"TRIC01"`
  - byte  `6`      : network tag (`1` = regtest, `2` = signet, `3` = mainnet)
  - byte  `7`      : KDF work factor exponent `k` (`rounds = 1 <<< k`; default `k = 12` = 4096 PBKDF2-HMAC-SHA512 rounds)
  - bytes `8..24`  : 16-byte random salt
  - bytes `24..36` : 12-byte random AES-GCM nonce
  - bytes `36..N`  : AES-256-GCM ciphertext of canonical 24-word mnemonic UTF-8
  - bytes `N..N+16`: 16-byte GCM authentication tag (AAD = header bytes `0..24`)

Wrong PIN attempts are counted in `attempts.bin` (1 byte). Reaching `maxFailedAttempts` (10)
triggers an automatic wipe of `vault.bin`, `descriptor.txt`, and `attempts.bin`. -/

namespace Tricorder.Vault

open Winnow

def magic : ByteArray := "TRIC01".toUTF8
def headerSize : Nat := 24
def minPinLength : Nat := 6
def maxPinLength : Nat := 12
def maxFailedAttempts : Nat := 10
def defaultKdfExp : UInt8 := 12 -- 4096 rounds PBKDF2-HMAC-SHA512 (snappy on pure Lean ARM64, paired with 10-try wipe + FBE)

def vaultFile : String := "vault.bin"
def attemptsFile : String := "attempts.bin"
def descriptorFile : String := "descriptor.txt"

def validPin (pin : String) : Bool :=
  let cs := pin.toList
  cs.length ≥ minPinLength && cs.length ≤ maxPinLength && cs.all (fun c => '0' ≤ c && c ≤ '9')

private def deriveKey (pin : String) (salt : ByteArray) (net : Network) (kdfExp : UInt8) : ByteArray :=
  let rounds := (1 <<< min kdfExp.toNat 20)
  let domain := ("tricorder-vault-v1:" ++ net.name ++ ":").toUTF8 ++ salt
  pbkdf2HmacSha512 pin.toUTF8 domain rounds 32

/-- Seals a validated 24-word mnemonic into `vault.bin` bytes using fresh 16-byte `salt` and 12-byte `nonce`. -/
def sealVault (net : Network) (pin : String) (words : Array String) (salt nonce : ByteArray)
    (kdfExp : UInt8 := defaultKdfExp) : Except String ByteArray := do
  unless validPin pin do throw s!"PIN must be {minPinLength}..{maxPinLength} digits"
  let _ ← Bip39Ascii.validate words
  unless salt.size == 16 do throw "salt must be 16 bytes"
  unless nonce.size == 12 do throw "nonce must be 12 bytes"
  let header := magic ++ ByteArray.mk #[net.tagByte, kdfExp] ++ salt
  let key := deriveKey pin salt net kdfExp
  let plaintext := (Bip39Ascii.joinWords words).toUTF8
  match AESGCM.«seal» key plaintext nonce header with
  | .error e => throw s!"vault encryption failed ({e.name})"
  | .ok box =>
    match box.combined with
    | none => throw "unexpected nonce size"
    | some combined => return header ++ combined

/-- Opens `vault.bin` bytes for `net` with `pin`, returning the validated 24-word mnemonic. -/
def openVault (net : Network) (pin : String) (blob : ByteArray) : Except String (Array String) := do
  unless blob.size ≥ headerSize + AESGCM.nonceSize + AESGCM.tagSize do
    throw "vault file is truncated"
  let gotMagic := blob.extract 0 6
  unless Secret.equal gotMagic magic do throw "not a Tricorder vault file"
  unless blob[6]! == net.tagByte do throw "vault belongs to a different Bitcoin network"
  let kdfExp := blob[7]!
  unless kdfExp ≥ 8 && kdfExp ≤ 20 do throw "unsupported KDF parameter"
  let header := blob.extract 0 headerSize
  let salt := blob.extract 8 24
  let combined := blob.extract headerSize blob.size
  let key := deriveKey pin salt net kdfExp
  let plaintext ← match AESGCM.openCombined key combined header with
    | .ok pt => pure pt
    | .error .authenticationFailure => throw "wrong PIN"
    | .error e => throw s!"vault open failed ({e.name})"
  let some sentence := String.fromUTF8? plaintext | throw "corrupt vault payload"
  let words := Bip39Ascii.splitSentence sentence
  let _ ← Bip39Ascii.validate words
  return words

/-- Encodes/decodes the persistent wrong-PIN counter (`attempts.bin`). -/
def encodeAttempts (n : Nat) : ByteArray := ByteArray.mk #[min n 255 |>.toUInt8]

def decodeAttempts (b : Option ByteArray) : Nat :=
  match b with
  | some arr => if arr.size ≥ 1 then arr[0]!.toNat else 0
  | none => 0

end Tricorder.Vault
