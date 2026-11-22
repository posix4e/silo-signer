import Winnow.Crypto
import Winnow.Keys.BIP39Wordlist

/-! # ASCII-only English BIP39 (24 words)

Uses Winnow's SHA-256, PBKDF2-HMAC-SHA512, and English wordlist without importing the 77 KiB Unicode
NFKD table: all 2048 English BIP39 words are lowercase ASCII. -/

namespace Tricorder.Bip39Ascii

open Winnow

def wordlist : Array String := Winnow.Keys.BIP39Wordlist.english

/-- Binary search in the sorted 2048-word English BIP39 wordlist. -/
def indexOf? (word : String) : Option Nat := Id.run do
  let w := word.toLower
  let mut lo := 0
  let mut hi := wordlist.size
  while lo < hi do
    let mid := (lo + hi) / 2
    let m := wordlist[mid]!
    if w == m then return some mid
    else if w < m then hi := mid else lo := mid + 1
  return none

/-- Words starting with `pref` (case-insensitive ASCII), up to `limit` matches, for on-screen restore. -/
def matchingPrefix (pref : String) (limit : Nat := 6) : Array String := Id.run do
  let p := pref.toLower
  if p.isEmpty then return #[]
  let mut out : Array String := #[]
  for w in wordlist do
    if w.startsWith p then
      out := out.push w
      if out.size ≥ limit then break
  return out

private def bitsOf (b : ByteArray) : Array Bool := Id.run do
  let mut out := Array.emptyWithCapacity (b.size * 8)
  for x in b.toList do
    for i in [0:8] do
      out := out.push ((x >>> (7 - i).toUInt8) &&& 1 == 1)
  return out

/-- 32 bytes of entropy -> 24 English BIP39 words (with 8-bit SHA-256 checksum). -/
def fromEntropy (entropy : ByteArray) : Except String (Array String) := do
  unless entropy.size == 32 do throw "BIP39 24-word mnemonic requires 32 bytes of entropy"
  let hash := sha256 entropy
  let bits := bitsOf entropy ++ bitsOf (hash.extract 0 1)
  let mut words := Array.emptyWithCapacity 24
  for w in [0:24] do
    let mut idx := 0
    for j in [0:11] do
      idx := idx * 2 + (if bits[w * 11 + j]! then 1 else 0)
    words := words.push wordlist[idx]!
  return words

/-- Validates 24 English BIP39 words and recovers the 32-byte entropy. -/
def validate (words : Array String) : Except String ByteArray := do
  unless words.size == 24 do throw s!"expected 24 words, got {words.size}"
  let mut bits := Array.emptyWithCapacity 264
  for w in words do
    match indexOf? w with
    | none => throw s!"word not in BIP39 list: {w}"
    | some idx =>
      for j in [0:11] do
        bits := bits.push ((idx >>> (10 - j)) % 2 == 1)
  let mut entropy := ByteArray.mk (Array.replicate 32 0)
  for i in [0:256] do
    if bits[i]! then
      let b := entropy[i / 8]! ||| (1 <<< (7 - (i % 8)).toUInt8)
      entropy := entropy.set! (i / 8) b
  let mut cs := 0
  for j in [0:8] do
    cs := cs * 2 + (if bits[256 + j]! then 1 else 0)
  let expected := (sha256 entropy)[0]!.toNat
  unless cs == expected do throw "BIP39 checksum mismatch"
  return entropy

/-- Normalizes a space-separated mnemonic string into lowercase ASCII words. -/
def splitSentence (text : String) : Array String :=
  ((text.splitOn " ").filter (!·.isEmpty)).map (·.trimAscii.toString.toLower) |>.toArray

/-- Canonical single-space mnemonic sentence. -/
def joinWords (words : Array String) : String :=
  " ".intercalate words.toList

/-- 24-word English BIP39 mnemonic -> 64-byte BIP39 seed via PBKDF2-HMAC-SHA512 (2048 rounds). -/
def toSeed (words : Array String) (passphrase : String := "") : ByteArray :=
  let sentence := (joinWords words).toLower
  pbkdf2HmacSha512 sentence.toUTF8 ("mnemonic" ++ passphrase).toUTF8 2048 64

end Tricorder.Bip39Ascii
