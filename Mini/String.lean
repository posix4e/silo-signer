import Mini.Lang
import Mini.Checked

/-! # Strings

A string is Lean's header, then three words (the byte count including a terminating zero, the room there is
for bytes, and the number of characters), then its UTF-8 bytes and the zero. Appending grows in place when the
caller holds the only reference and there is room, and copies otherwise; one marked linear stops the machine
rather than be copied while someone else holds it.

The rules of UTF-8 are not here: they are Lean (`Runtime/Utf8.lean`). This program knows where a string's
bytes are and how many there are; it hands over the bytes in question, as numbers, and acts on the answer.

Lean addresses a character by the byte offset where its encoding starts, and says what happens at offsets
that are out of range or in the middle of a character. Where that matters below, the rules are Lean's, case
for case. -/

namespace Mini.Str

def object : String := "lean_object *"
def stringHeader : Expr := .lit (UInt64.ofNat (1 + 249 * 2 ^ 56))
def linearMark : Expr := .lit (UInt64.ofNat (2 ^ 55))
/-- What `utf8_length` gives for bytes that are not UTF-8: no count of characters can be this. -/
def notUtf8 : Expr := .lit 0xFFFFFFFFFFFFFFFF
/-- `lean_char_default_value`, the character `'A'`. -/
def defaultChar : Expr := 65

def sizeOf (s : Expr) : Expr := .load (s + 8)
def capacityOf (s : Expr) : Expr := .load (s + 16)
def lengthOf (s : Expr) : Expr := .load (s + 24)
def bytes (s : Expr) : Expr := s + 32
def exclusive (s : Expr) : Expr := Expr.eq (Expr.and (.load s) (.lit 0xFFFFFFFF)) 1
def linear (s : Expr) : Expr := Expr.ne (Expr.and (.load s) linearMark) 0
def scalar (o : Expr) : Expr := Expr.ne (Expr.and o 1) 0
def unbox (o : Expr) : Expr := Expr.shr o 1
def box (n : Expr) : Expr := Expr.or (Expr.shl n 1) 1
def keepMark (from_ to : String) : Stmt :=
  .branch (linear from_) [.store to (Expr.or (.load to) linearMark)] []
def copyBytes (to from_ count : Expr) : Stmt := .callOther none "memcpy" [to, from_, count]
def refuseLinear (s : Expr) : Stmt :=
  .branch (linear s) [.stop "a value marked linear was used where it would have to be copied"] []
/-- Whether a character was found, in what `rt_utf8_read` gives. -/
def found (word : Expr) : Expr := Expr.ne (Expr.shr word 32) 0
def character (word : Expr) : Expr := Expr.and word 0xFFFFFFFF

def newString : Function where
  name := "new_string"
  parameters := ["size", "capacity", "length"]
  body := [
    .call (some "room") "add_checked" [32, "capacity"],
    .callOther (some "r") "lean_alloc_object" ["room"],
    .store "r" stringHeader,
    .store ("r" + 8) "size",
    .store ("r" + 16) "capacity",
    .store ("r" + 24) "length",
    .give "r"]

def byteAt : Function where
  name := "byte_at"
  about := "Byte `i` of the `size` bytes at `s`, or zero past the end."
  parameters := ["s", "size", "i"]
  body := [.branch (Expr.lt "i" "size") (Stmt.inBounds "i" "size" ++ [.give (.part 1 ("s" + "i"))]) [], .give 0]

/-- The four bytes from `at`, as `byte_at` gives them, into `b0` to `b3`. -/
def fourBytes (s size at_ : Expr) : List Stmt := [
  .call (some "b0") "byte_at" [s, size, at_],
  .call (some "b1") "byte_at" [s, size, at_ + 1],
  .call (some "b2") "byte_at" [s, size, at_ + 2],
  .call (some "b3") "byte_at" [s, size, at_ + 3]]

/-- High bit of every byte of a word. -/
def highBits : Expr := .lit 0x8080808080808080

def eightAscii : Function where
  name := "eight_ascii"
  about := "Whether the eight bytes from `at` are all there and all ASCII, read as one word: no byte with its high bit\nset. The trick glibc, musl and simdjson use to skip ASCII eight bytes at a time. Unlike theirs, the word is\nonly read when all eight bytes belong to the string; reading past the end, which they get away with by\nnot crossing a page, is a read of memory nothing wrote, and the language refuses it."
  parameters := ["s", "size", "at"]
  body := [
    .branch (Expr.lt "size" ("at" + 8)) [.give 0] [],
    .give (Expr.eq (Expr.and (.load ("s" + "at")) highBits) 0)]

def utf8Length : Function where
  name := "utf8_length"
  about := "The number of characters in `size` bytes of well-formed UTF-8, or all ones if they are not well-formed."
  parameters := ["s", "size"]
  body := [
    .set "count" 0,
    .set "at" 0,
    .loop (Expr.lt "at" "size") [
      .call (some "ascii") "eight_ascii" ["s", "size", "at"],
      .branch (Expr.ne "ascii" 0) [.set "at" ("at" + 8), .set "count" ("count" + 8)]
        (fourBytes "s" "size" "at" ++ [
          .callOther (some "taken") "rt_utf8_strict" ["b0", "b1", "b2", "b3", "size" - "at"],
          .branch (Expr.eq "taken" 0) [.give notUtf8] [],
          .set "at" ("at" + "taken"),
          .set "count" ("count" + 1)])],
    .give "count"]

def scalarSize : Function where
  name := "scalar_size"
  parameters := ["c"]
  body := [.callOther (some "encoded") "rt_utf8_write" ["c"], .give (Expr.shr "encoded" 32)]

def putScalar : Function where
  name := "put_scalar"
  about := "The UTF-8 encoding of `c` written at `to`; gives how many bytes that was (one to four)."
  parameters := ["to", "c"]
  body := [
    .callOther (some "encoded") "rt_utf8_write" ["c"],
    .set "count" (Expr.shr "encoded" 32),
    .set "i" 0,
    .loop (Expr.lt "i" "count") [
      .storePart 1 ("to" + "i") (Expr.shr "encoded" (8 * "i")),
      .set "i" ("i" + 1)],
    .give "count"]

def mkUnchecked : Function where
  name := "lean_mk_string_unchecked"
  seen := some { result := object, parameters := ["char const *", "size_t", "size_t"] }
  parameters := ["s", "size", "length"]
  body := [
    .call (some "with_zero") "add_checked" ["size", 1],
    .call (some "r") "new_string" ["with_zero", "with_zero", "length"],
    copyBytes (bytes "r") "s" "size",
    .storePart 1 (bytes "r" + "size") 0,
    .give "r"]

def mk : Function where
  name := "lean_mk_string"
  about := "A string from a C string. Compiled Lean passes its own literals here, which are UTF-8; anything else stops\nthe machine. (Lean's runtime repairs bad bytes with U+FFFD; nothing here should ever need that.)"
  seen := some { result := object, parameters := ["char const *"] }
  parameters := ["s"]
  body := [
    .callOther (some "size") "strlen" ["s"],
    .call (some "length") "utf8_length" ["s", "size"],
    .branch (Expr.eq "length" notUtf8) [.stop "lean_mk_string was given bytes that are not UTF-8"] [],
    .call (some "r") "lean_mk_string_unchecked" ["s", "size", "length"],
    .give "r"]

/-- The character in a list cell, and the cell after it. -/
def head (cell : Expr) : Expr := unbox (.load (cell + 8))
def tail (cell : Expr) : Expr := .load (cell + 16)

def ofList : Function where
  name := "lean_string_mk"
  about := "`String.mk`: a string from a list of characters. Gives up the list."
  seen := some { result := object, parameters := [object] }
  parameters := ["chars"]
  body := [
    .set "size" 0,
    .set "length" 0,
    .set "at" "chars",
    .loop (Expr.eq (Expr.and "at" 1) 0) [
      .call (some "n") "scalar_size" [head "at"],
      .call (some "size") "add_checked" ["size", "n"],
      .set "length" ("length" + 1),
      .set "at" (tail "at")],
    .call (some "with_zero") "add_checked" ["size", 1],
    .call (some "r") "new_string" ["with_zero", "with_zero", "length"],
    .set "to" (bytes "r"),
    .set "at" "chars",
    .loop (Expr.eq (Expr.and "at" 1) 0) [
      .call (some "n") "put_scalar" ["to", head "at"],
      .set "to" ("to" + "n"),
      .set "at" (tail "at")],
    .storePart 1 "to" 0,
    .callOther none "lean_dec" ["chars"],
    .give "r"]

def copyString : Function where
  name := "copy_string"
  about := "A copy of `s` with room for `capacity` bytes. Gives up `s`."
  parameters := ["s", "capacity"]
  body := [
    .set "size" (sizeOf "s"),
    .call (some "r") "new_string" ["size", "capacity", lengthOf "s"],
    keepMark "s" "r",
    copyBytes (bytes "r") (bytes "s") "size",
    .callOther none "lean_dec_ref" ["s"],
    .give "r"]

def withRoom : Function where
  name := "string_with_room"
  about := "`s`, held by the caller alone, with room for `extra` more bytes."
  parameters := ["s", "extra"]
  body := [
    .set "size" (sizeOf "s"),
    .set "capacity" (capacityOf "s"),
    .call (some "needed") "add_checked" ["size", "extra"],
    .branch (Expr.le "needed" "capacity") [.give "s"] [],
    .call (some "capacity") "add_checked" ["capacity", "needed"],
    .call (some "r") "new_string" ["size", "capacity", lengthOf "s"],
    keepMark "s" "r",
    copyBytes (bytes "r") (bytes "s") "size",
    .callOther none "lean_free_object" ["s"],
    .give "r"]

def append : Function where
  name := "lean_string_append"
  about := "`s1 ++ s2`. Gives up `s1`, borrows `s2`."
  seen := some { result := object, parameters := [object, object] }
  parameters := ["s1", "s2"]
  body := [
    .set "size1" (sizeOf "s1"),
    .set "size2" (sizeOf "s2"),
    .set "new_length" (lengthOf "s1" + lengthOf "s2"),
    .call (some "new_size") "add_checked" ["size1", "size2"],
    .set "new_size" ("new_size" - 1),
    .branch (exclusive "s1")
      [.call (some "r") "string_with_room" ["s1", "size2" - 1]]
      [refuseLinear "s1",
       .call (some "capacity") "mul_checked" ["new_size", 2],
       .call (some "r") "copy_string" ["s1", "capacity"]],
    copyBytes (bytes "r" + "size1" - 1) (bytes "s2") ("size2" - 1),
    .store ("r" + 8) "new_size",
    .store ("r" + 24) "new_length",
    .storePart 1 (bytes "r" + "new_size" - 1) 0,
    .give "r"]

def eqCold : Function where
  name := "lean_string_eq_cold"
  about := "Equality of two strings already known to have the same byte count."
  seen := some { result := "bool", parameters := [object, object] }
  parameters := ["s1", "s2"]
  body := [
    .callOther (some "differ") "memcmp" [bytes "s1", bytes "s2", sizeOf "s1"],
    .give (Expr.eq "differ" 0)]

def ofSize : Function where
  name := "lean_string_of_usize"
  about := "A number in decimal."
  seen := some { result := object, parameters := ["size_t"] }
  parameters := ["n"]
  body := [
    .set "digits" 1,
    .set "rest" ("n" / 10),
    .loop (Expr.ne "rest" 0) [.set "digits" ("digits" + 1), .set "rest" ("rest" / 10)],
    .call (some "r") "new_string" ["digits" + 1, "digits" + 1, "digits"],
    .set "at" "digits",
    .set "rest" "n",
    .loop (Expr.ne "at" 0) [
      .set "at" ("at" - 1),
      .storePart 1 (bytes "r" + "at") (48 + ("rest" - "rest" / 10 * 10)),
      .set "rest" ("rest" / 10)],
    .storePart 1 (bytes "r" + "digits") 0,
    .give "r"]

def charAt : Function where
  name := "char_at"
  about := "What `rt_utf8_read` says of the character whose encoding starts at byte `i` of the `size` bytes at `str`."
  parameters := ["str", "size", "i"]
  body := fourBytes "str" "size" "i" ++ [
    .callOther (some "read") "rt_utf8_read" ["b0", "b1", "b2", "b3", "size" - "i"],
    .give "read"]

def get : Function where
  name := "lean_string_utf8_get"
  about := "`String.get`: the character at byte position `i`, or the default character if there is none. A position\nthat is not a small number is past the end of any string that can exist."
  seen := some { result := "uint32_t", parameters := [object, object] }
  parameters := ["s", "i0"]
  body := [
    .branch (scalar "i0") [] [.give defaultChar],
    .set "i" (unbox "i0"),
    .set "size" (sizeOf "s" - 1),
    .branch (Expr.le "size" "i") [.give defaultChar] [],
    .call (some "read") "char_at" [bytes "s", "size", "i"],
    .branch (found "read") [.give (character "read")] [],
    .give defaultChar]

def getFastCold : Function where
  name := "lean_string_utf8_get_fast_cold"
  about := "The slow half of the inline `String.get`: `c` is the byte at `i` and is not ASCII."
  seen := some { result := "uint32_t", parameters := ["char const *", "size_t", "size_t", "unsigned char"] }
  parameters := ["str", "i", "size", "c"]
  body := [
    .branch (Expr.ne (Expr.and "c" 0x80) 0)
      [.call (some "read") "char_at" ["str", "size", "i"],
       .branch (found "read") [.give (character "read")] []] [],
    .give defaultChar]

def next : Function where
  name := "lean_string_utf8_next"
  about := "`String.next`: the byte position after the character at `i`."
  seen := some { result := object, parameters := [object, object] }
  parameters := ["s", "i0"]
  body := [
    .branch (scalar "i0") [] [.callOther (some "r") "lean_nat_add" ["i0", box 1], .give "r"],
    .set "i" (unbox "i0"),
    .set "size" (sizeOf "s" - 1),
    .branch (Expr.le "size" "i") [.callOther (some "r") "lean_usize_to_nat" ["i" + 1], .give "r"] [],
    .set "at" "i"] ++ Stmt.inBounds "at" "size" ++ [
    .callOther (some "n") "rt_utf8_claims" [.part 1 (bytes "s" + "at"), 4],
    .give (box ("i" + "n"))]

def nextFastCold : Function where
  name := "lean_string_utf8_next_fast_cold"
  seen := some { result := object, parameters := ["size_t", "unsigned char"] }
  parameters := ["i", "c"]
  body := [.callOther (some "n") "rt_utf8_claims" ["c", 4], .give (box ("i" + "n"))]

def startsCharacter : Function where
  name := "starts_character"
  parameters := ["c"]
  body := [.give (Expr.or (Expr.or (Expr.eq (Expr.and "c" 0x80) 0) (Expr.eq (Expr.and "c" 0xe0) 0xc0))
                          (Expr.or (Expr.eq (Expr.and "c" 0xf0) 0xe0) (Expr.eq (Expr.and "c" 0xf8) 0xf0)))]

def fromTrusted : Function where
  name := "string_from_trusted"
  about := "A string from bytes taken out of an existing string: characters are counted by their leading bytes."
  parameters := ["from", "size"]
  body := [
    .set "length" 0,
    .set "i" 0,
    .loop (Expr.lt "i" "size") [
      .call (some "ascii") "eight_ascii" ["from", "size", "i"],
      .branch (Expr.ne "ascii" 0) [.set "i" ("i" + 8), .set "length" ("length" + 8)]
        [.callOther (some "n") "rt_utf8_claims" [.part 1 ("from" + "i"), 6],
         .set "i" ("i" + "n"),
         .set "length" ("length" + 1)]],
    .call (some "r") "lean_mk_string_unchecked" ["from", "size", "length"],
    .give "r"]

def extract : Function where
  name := "lean_string_utf8_extract"
  about := "`String.extract`: the bytes from position `b` up to `e`."
  seen := some { result := object, parameters := [object, object, object] }
  parameters := ["s", "b0", "e0"]
  body := [
    .set "b" (unbox "b0"),
    .branch (scalar "b0") [] [.set "b" 0xFFFFFFFFFFFFFFFF],
    .set "e" (unbox "e0"),
    .branch (scalar "e0") [] [.set "e" 0xFFFFFFFFFFFFFFFF],
    .set "size" (sizeOf "s" - 1),
    .branch (Expr.or (Expr.le "e" "b") (Expr.le "size" "b"))
      [.call (some "r") "lean_mk_string_unchecked" [bytes "s", 0, 0], .give "r"] [],
    .set "at" "b"] ++ Stmt.inBounds "at" "size" ++ [
    .call (some "starts") "starts_character" [.part 1 (bytes "s" + "at")],
    .branch (Expr.eq "starts" 0) [.call (some "r") "lean_mk_string_unchecked" [bytes "s", 0, 0], .give "r"] [],
    .branch (Expr.lt "size" "e") [.set "e" "size"] [],
    .branch (Expr.lt "e" "size")
      (Stmt.inBounds "e" "size" ++ [.call (some "starts") "starts_character" [.part 1 (bytes "s" + "e")],
       .branch (Expr.eq "starts" 0) [.set "e" "size"] []]) [],
    .call (some "r") "string_from_trusted" [bytes "s" + "b", "e" - "b"],
    .give "r"]

def push : Function where
  name := "lean_string_push"
  about := "`String.push`. Gives up `s`."
  seen := some { result := object, parameters := [object, "uint32_t"] }
  parameters := ["s", "c"]
  body := [
    .set "size" (sizeOf "s"),
    .branch (exclusive "s")
      [.call (some "r") "string_with_room" ["s", 5]]
      [refuseLinear "s",
       .call (some "capacity") "add_checked" ["size", 5],
       .call (some "capacity") "mul_checked" ["capacity", 2],
       .call (some "r") "copy_string" ["s", "capacity"]],
    .call (some "added") "put_scalar" [bytes "r" + "size" - 1, "c"],
    .store ("r" + 8) ("size" + "added"),
    .store ("r" + 24) (lengthOf "r" + 1),
    .storePart 1 (bytes "r" + "size" + "added" - 1) 0,
    .give "r"]

def toList : Function where
  name := "lean_string_data"
  about := "`String.data`: the characters as a list. Gives up `s`. Bytes that do not form a character each count as\none, the way Lean decodes."
  seen := some { result := object, parameters := [object] }
  parameters := ["s"]
  body := [
    .set "size" (sizeOf "s" - 1),
    .set "first" (box 0),
    .set "last" 0,
    .set "i" 0,
    .loop (Expr.lt "i" "size") [
      .call (some "read") "char_at" [bytes "s", "size", "i"],
      .branch (found "read")
        [.set "c" (character "read"),
         .call (some "n") "scalar_size" ["c"],
         .set "i" ("i" + "n")]
        [.set "c" (.part 1 (bytes "s" + "i")),
         .set "i" ("i" + 1)],
      .callOther (some "cell") "lean_alloc_ctor" [1, 2, 0],
      .store ("cell" + 8) (box "c"),
      .store ("cell" + 16) (box 0),
      .branch (Expr.eq "last" 0) [.set "first" "cell"] [.store ("last" + 16) "cell"],
      .set "last" "cell"],
    .callOther none "lean_dec_ref" ["s"],
    .give "first"]

def toBytes : Function where
  name := "lean_string_to_utf8"
  about := "`String.toUTF8`: the bytes without the terminating zero."
  seen := some { result := object, parameters := [object] }
  parameters := ["s"]
  body := [
    .set "size" (sizeOf "s" - 1),
    .callOther (some "r") "lean_alloc_sarray" [1, "size", "size"],
    copyBytes ("r" + 24) (bytes "s") "size",
    .give "r"]

def hash : Function where
  name := "lean_string_hash"
  seen := some { result := "uint64_t", parameters := [object] }
  parameters := ["s"]
  body := [.callOther (some "h") "rt_hash_bytes" [bytes "s", sizeOf "s" - 1, 11], .give "h"]

def sameBytes : Function where
  name := "lean_string_memcmp"
  about := "Whether `len` bytes of two strings, from the given offsets, are equal. The offsets and length come with\nproofs that they are in range."
  seen := some { result := "uint8_t", parameters := [object, object, object, object, object] }
  parameters := ["s1", "s2", "lstart", "rstart", "len"]
  body := [
    .callOther (some "differ") "memcmp" [bytes "s1" + unbox "lstart", bytes "s2" + unbox "rstart", unbox "len"],
    .give (Expr.eq "differ" 0)]

def less : Function where
  name := "lean_string_lt"
  about := "`s1 < s2`: by bytes, a prefix sorting before anything it is a prefix of."
  seen := some { result := "bool", parameters := [object, object] }
  parameters := ["s1", "s2"]
  body := [
    .set "size1" (sizeOf "s1" - 1),
    .set "size2" (sizeOf "s2" - 1),
    .set "shorter" "size1",
    .branch (Expr.lt "size2" "size1") [.set "shorter" "size2"] [],
    .set "i" 0,
    -- Equal words are skipped eight bytes at a time; the first that differ are then gone through a byte at a
    -- time, from where they start.
    .set "words" 1,
    .loop (Expr.and (Expr.le ("i" + 8) "shorter") "words") [
      .branch (Expr.eq (.load (bytes "s1" + "i")) (.load (bytes "s2" + "i"))) [.set "i" ("i" + 8)] [.set "words" 0]],
    .loop (Expr.lt "i" "shorter") [
      .set "a" (.part 1 (bytes "s1" + "i")),
      .set "b" (.part 1 (bytes "s2" + "i")),
      .branch (Expr.ne "a" "b") [.give (Expr.lt "a" "b")] [],
      .set "i" ("i" + 1)],
    .give (Expr.lt "size1" "size2")]

def program : Program where
  about := "Strings."
  preamble := "#include \"rt.h\"\n\n/* The rules of UTF-8, in Lean (Runtime/Utf8.lean). */\nuint8_t rt_utf8_strict(uint8_t, uint8_t, uint8_t, uint8_t, size_t);\nuint64_t rt_utf8_read(uint8_t, uint8_t, uint8_t, uint8_t, size_t);\nuint64_t rt_utf8_write(uint32_t);\nuint8_t rt_utf8_claims(uint8_t, uint8_t);\n\n/* Init's, which the runtime provides. */\nlean_obj_res lean_string_to_utf8(b_lean_obj_arg s);\n"
  globals := []
  arrays := []
  others := [
    ("lean_alloc_object", { result := object, parameters := ["size_t"] }),
    ("lean_free_object", { result := "void", parameters := [object] }),
    ("lean_alloc_ctor", { result := object, parameters := ["unsigned", "unsigned", "unsigned"] }),
    ("lean_alloc_sarray", { result := object, parameters := ["unsigned", "size_t", "size_t"] }),
    ("lean_dec", { result := "void", parameters := [object] }),
    ("lean_dec_ref", { result := "void", parameters := [object] }),
    ("lean_nat_add", { result := object, parameters := [object, object] }),
    ("lean_usize_to_nat", { result := object, parameters := ["size_t"] }),
    ("memcpy", { result := "void *", parameters := ["void *", "void const *", "size_t"] }),
    ("memcmp", { result := "int", parameters := ["void const *", "void const *", "size_t"] }),
    ("strlen", { result := "size_t", parameters := ["char const *"] }),
    ("rt_hash_bytes", { result := "uint64_t", parameters := ["uint8_t const *", "size_t", "uint64_t"] }),
    ("rt_utf8_strict", { result := "uint8_t", parameters := ["uint8_t", "uint8_t", "uint8_t", "uint8_t", "size_t"] }),
    ("rt_utf8_read", { result := "uint64_t", parameters := ["uint8_t", "uint8_t", "uint8_t", "uint8_t", "size_t"] }),
    ("rt_utf8_write", { result := "uint64_t", parameters := ["uint32_t"] }),
    ("rt_utf8_claims", { result := "uint8_t", parameters := ["uint8_t", "uint8_t"] })]
  functions := Checked.functions ++ [newString, byteAt, eightAscii, utf8Length, scalarSize, putScalar, mkUnchecked, mk, ofList, copyString,
    withRoom, append, eqCold, ofSize, charAt, get, getFastCold, next, nextFastCold, startsCharacter,
    fromTrusted, extract, push, toList, toBytes, hash, sameBytes, less]

end Mini.Str
