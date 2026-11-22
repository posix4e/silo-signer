import Mini.Lang

/-! # What a number too large for a word is in memory

Compiled Lean keeps a natural number below 2^63, and an integer that fits in 32 bits, in a tagged word: the
number shifted up one bit with the lowest bit set. For anything else it calls the functions here with what
it has, tagged words or objects, and expects the same back.

A big number is one heap object: Lean's eight-byte header, then four bytes that are 1 for a number below
zero, four bytes of count, and that many 32-bit limbs, least significant first. Two rules hold for every
number that leaves this program, and compiled Lean depends on them (it decides that two small numbers are
equal by comparing the words), so a number that arrives breaking either one stops the machine:

  - a natural number below 2^63 is a tagged word, never an object; so is an integer in the 32-bit range;
  - an object's top limb is not zero.

The arithmetic is `Runtime/Big.lean`, on Lean arrays of limbs. This program copies an argument's limbs into
such an array, calls it, and makes the result out of the array that comes back. An array is Lean's header,
its size, its capacity, and then its elements, each limb a tagged word. -/

namespace Mini.Number

def top : Expr := .lit 0x80000000
def low32 : Expr := .lit 0xFFFFFFFF
/-- A header with one reference and this kind of object. -/
def header (kind : Nat) : Expr := .lit (UInt64.ofNat (1 + kind * 2 ^ 56))
def arrayKind : Nat := 246
def numberKind : Nat := 250

def box (e : Expr) : Expr := Expr.or (Expr.shl e 1) 1
def unbox (e : Expr) : Expr := Expr.shr e 1
def isWord (e : Expr) : Expr := Expr.ne (Expr.and e 1) 0
/-- Element `i` of an array of limbs. -/
def limbAt (array i : Expr) : Expr := unbox (.load (array + 24 + i * 8))
def sizeOf (array : Expr) : Expr := .load (array + 8)
/-- Parts of a big-number object. -/
def negativeOf (o : Expr) : Expr := .part 4 (o + 8)
def countOf (o : Expr) : Expr := .part 4 (o + 12)
def objectLimb (o i : Expr) : Expr := .part 4 (o + 16 + i * 4)

def drop (array : Expr) : Stmt := .callOther none "lean_dec" [array]
def outOfMemory : Stmt := .outside none "lean_internal_panic_out_of_memory()"

def arrayNew : Function where
  name := "array_new"
  about := "An array of `count` elements, for the arithmetic. The elements are the caller's to write."
  parameters := ["count"]
  body := [
    .callOther (some "array") "lean_alloc_object" [24 + "count" * 8],
    .store "array" (header arrayKind),
    .store ("array" + 8) "count",
    .store ("array" + 16) "count",
    .give "array"]

def limbsOfWord : Function where
  name := "limbs_of_word"
  about := "The limbs of a number that fits in a word."
  parameters := ["value"]
  body := [
    .set "count" 0,
    .branch (Expr.ne "value" 0) [.set "count" 1] [],
    .branch (Expr.lt low32 "value") [.set "count" 2] [],
    .call (some "array") "array_new" ["count"],
    .branch (Expr.lt 0 "count") [.store ("array" + 24) (box (Expr.and "value" low32))] [],
    .branch (Expr.lt 1 "count") [.store ("array" + 32) (box (Expr.shr "value" 32))] [],
    .give "array"]

def checked : Function where
  name := "checked"
  about := "The count of limbs in an object handed in as a number. The checks cost a few comparisons and can only\nfail if this program has a fault or memory has been damaged: nothing else makes these objects. Carrying on\nwould mean wrong arithmetic, so the machine stops instead."
  parameters := ["o"]
  body := [
    .set "count" (countOf "o"),
    .branch (Expr.or (Expr.ne (Expr.shr (.load "o") 56) (.lit (UInt64.ofNat numberKind))) (Expr.eq "count" 0))
      [.stop "something that is not a big number, or not a well-formed one, was used as a number"] [],
    .branch (Expr.or (Expr.eq (objectLimb "o" ("count" - 1)) 0) (Expr.lt 1 (negativeOf "o")))
      [.stop "something that is not a big number, or not a well-formed one, was used as a number"] [],
    .give "count"]

def limbsOfObject : Function where
  name := "limbs_of_object"
  parameters := ["o", "count"]
  body := [
    .call (some "array") "array_new" ["count"],
    .set "i" 0,
    .loop (Expr.lt "i" "count") [
      .store ("array" + 24 + "i" * 8) (box (objectLimb "o" "i")),
      .set "i" ("i" + 1)],
    .give "array"]

def natLimbs : Function where
  name := "nat_limbs"
  about := "The limbs of a natural-number argument. An object has to be 2^63 or more."
  parameters := ["o"]
  body := [
    .branch (isWord "o") [.call (some "array") "limbs_of_word" [unbox "o"], .give "array"] [],
    .call (some "count") "checked" ["o"],
    .branch (Expr.or (Expr.ne (negativeOf "o") 0) (Expr.lt "count" 2))
      [.stop "an object used as a natural number holds a negative number or one below 2^63"] [],
    .branch (Expr.and (Expr.eq "count" 2) (Expr.lt (objectLimb "o" 1) top))
      [.stop "an object used as a natural number holds a negative number or one below 2^63"] [],
    .call (some "array") "limbs_of_object" ["o", "count"],
    .give "array"]

def intSign : Function where
  name := "int_sign"
  about := "1 if an integer argument is below zero, otherwise 0. A tagged word holds the 32 bits of a value from\n-2^31 to 2^31 - 1."
  parameters := ["o"]
  body := [
    .branch (isWord "o") [.give (Expr.and (Expr.shr "o" 32) 1)] [],
    .give (negativeOf "o")]

def intLimbs : Function where
  name := "int_limbs"
  about := "The limbs of an integer argument, without its sign. An object has to be outside the 32-bit range."
  parameters := ["o"]
  body := [
    .branch (isWord "o")
      [.set "value" (Expr.and (unbox "o") low32),
       -- Negated within 32 bits, so that the most negative value comes out as 2^31.
       .branch (Expr.le top "value") [.set "value" (Expr.and (0 - "value") low32)] [],
       .call (some "array") "limbs_of_word" ["value"],
       .give "array"] [],
    .call (some "count") "checked" ["o"],
    .branch (Expr.eq "count" 1)
      [.set "only" (objectLimb "o" 0),
       .branch (Expr.or (Expr.lt "only" top) (Expr.and (Expr.ne (negativeOf "o") 0) (Expr.eq "only" top)))
         [.stop "an object used as an integer holds a number that fits in 32 bits"] []] [],
    .call (some "array") "limbs_of_object" ["o", "count"],
    .give "array"]

def trimmed : Function where
  name := "trimmed"
  about := "`count` without the zero limbs at the top of an array."
  parameters := ["array", "count"]
  body := [
    .loop (Expr.lt 0 "count") [
      .branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [],
      .set "count" ("count" - 1)],
    .give "count"]

def bigNew : Function where
  name := "big_new"
  about := "The object for a number that does not fit in a tagged word: the first `count` limbs of an array, whose\ntop one is not zero."
  parameters := ["negative", "array", "count"]
  body := [
    .branch (Expr.lt low32 "count") [outOfMemory] [],
    .callOther (some "o") "lean_alloc_object" [16 + "count" * 4],
    .store "o" (header numberKind),
    .storePart 4 ("o" + 8) "negative",
    .storePart 4 ("o" + 12) "count",
    .set "i" 0,
    .loop (Expr.lt "i" "count") [
      .storePart 4 ("o" + 16 + "i" * 4) (limbAt "array" "i"),
      .set "i" ("i" + 1)],
    .give "o"]

def natResult : Function where
  name := "nat_result"
  about := "The natural number with the first `count` limbs of an array, as Lean holds it: a tagged word below 2^63,\nan object from there up."
  parameters := ["array", "count"]
  body := [
    .call (some "count") "trimmed" ["array", "count"],
    .branch (Expr.eq "count" 0) [.give (box 0)] [],
    .branch (Expr.eq "count" 1) [.give (box (limbAt "array" 0))] [],
    .branch (Expr.and (Expr.eq "count" 2) (Expr.lt (limbAt "array" 1) top))
      [.give (box (Expr.or (Expr.shl (limbAt "array" 1) 32) (limbAt "array" 0)))] [],
    .call (some "o") "big_new" [0, "array", "count"],
    .give "o"]

def intResult : Function where
  name := "int_result"
  about := "The integer with this sign and the first `count` limbs of an array, as Lean holds it: a tagged word\nholding the 32 bits of a value from -2^31 to 2^31 - 1, an object for anything else."
  parameters := ["negative", "array", "count"]
  body := [
    .call (some "count") "trimmed" ["array", "count"],
    .branch (Expr.eq "count" 0) [.give (box 0)] [],
    .branch (Expr.eq "count" 1)
      [.set "only" (limbAt "array" 0),
       .branch (Expr.and (Expr.eq "negative" 0) (Expr.lt "only" top)) [.give (box "only")] [],
       .branch (Expr.and (Expr.ne "negative" 0) (Expr.le "only" top)) [.give (box (Expr.and (0 - "only") low32))] []] [],
    .call (some "o") "big_new" ["negative", "array", "count"],
    .give "o"]

def natFrom : Function where
  name := "nat_from"
  about := "The natural number in an array the arithmetic returned. Gives the array up."
  parameters := ["array"]
  body := [
    .call (some "result") "nat_result" ["array", sizeOf "array"],
    drop "array",
    .give "result"]

def intFrom : Function where
  name := "int_from"
  about := "The integer in an array the arithmetic returned: its limbs, then one more element that is 1 if it is\nbelow zero. Gives the array up."
  parameters := ["array"]
  body := [
    .set "count" (sizeOf "array"),
    .branch (Expr.eq "count" 0) [.stop "the arithmetic returned an integer without its sign"] [],
    .call (some "result") "int_result" [Expr.ne (limbAt "array" ("count" - 1)) 0, "array", "count" - 1],
    drop "array",
    .give "result"]

def natOfWord : Function where
  name := "nat_of_word"
  parameters := ["value"]
  body := [
    .call (some "array") "limbs_of_word" ["value"],
    .call (some "result") "nat_from" ["array"],
    .give "result"]

def intOfWord : Function where
  name := "int_of_word"
  parameters := ["negative", "value"]
  body := [
    .call (some "array") "limbs_of_word" ["value"],
    .call (some "result") "int_result" ["negative", "array", sizeOf "array"],
    drop "array",
    .give "result"]

def log2 : Function where
  name := "log2"
  about := "The position of the highest set bit of the number in an array with no zero limb on top; 0 for 0."
  parameters := ["array"]
  body := [
    .set "count" (sizeOf "array"),
    .branch (Expr.eq "count" 0) [.give 0] [],
    .set "limb" (limbAt "array" ("count" - 1)),
    .set "result" (("count" - 1) * 32),
    .loop (Expr.le 2 "limb") [.set "limb" ("limb" / 2), .set "result" ("result" + 1)],
    .give "result"]

def magnitudeLow : Function where
  name := "magnitude_low"
  about := "The lowest 64 bits of an integer argument without its sign."
  parameters := ["o"]
  body := [
    .branch (isWord "o")
      [.set "value" (Expr.and (unbox "o") low32),
       .branch (Expr.le top "value") [.set "value" (Expr.and (0 - "value") low32)] [],
       .give "value"] [],
    .call (some "count") "checked" ["o"],
    .set "value" (objectLimb "o" 0),
    .branch (Expr.lt 1 "count") [.set "value" (Expr.or "value" (Expr.shl (objectLimb "o" 1) 32))] [],
    .give "value"]

def modulo : Function where
  name := "modulo"
  about := "An integer argument modulo 2^64: for a number below zero, what its two's complement form keeps in 64\nbits. The narrower types keep the low bits of this."
  parameters := ["o"]
  body := [
    .call (some "value") "magnitude_low" ["o"],
    .call (some "negative") "int_sign" ["o"],
    .branch (Expr.ne "negative" 0) [.give (0 - "value")] [],
    .give "value"]

/-! The functions compiled Lean calls, under the names `<lean/lean.h>` declares, and the four `rt/nat.c` does. -/

def object : String := "lean_object *"
def two : Seen := { result := object, parameters := [object, object] }
def asBool : Seen := { result := "bool", parameters := [object, object] }

def natOperation (name arithmetic about : String) : Function where
  name := name
  about := about
  seen := some two
  parameters := ["a1", "a2"]
  body := [
    .call (some "a") "nat_limbs" ["a1"],
    .call (some "b") "nat_limbs" ["a2"],
    .callOther (some "array") arithmetic ["a", "b"],
    .call (some "result") "nat_from" ["array"],
    .give "result"]

def natOrder (name : String) (holds : Expr → Expr) : Function where
  name := name
  seen := some asBool
  parameters := ["a1", "a2"]
  body := [
    .call (some "a") "nat_limbs" ["a1"],
    .call (some "b") "nat_limbs" ["a2"],
    .callOther (some "order") "rt_big_compare" ["a", "b"],
    .give (holds "order")]

/-- `minus` turns the second number's sign round first: a - b is a + (-b), and zero stays as it is. -/
def intOperation (name arithmetic : String) (minus : Bool) (about : String := "") : Function where
  name := name
  about := about
  seen := some two
  parameters := ["a1", "a2"]
  body := [
    .call (some "a") "int_limbs" ["a1"],
    .call (some "sign1") "int_sign" ["a1"],
    .call (some "b") "int_limbs" ["a2"],
    .call (some "sign2") "int_sign" ["a2"]] ++
    (if minus then [.branch (Expr.ne (sizeOf "b") 0) [.set "sign2" (1 - "sign2")] []] else []) ++ [
    .callOther (some "array") arithmetic ["sign1", "a", "sign2", "b"],
    .call (some "result") "int_from" ["array"],
    .give "result"]

def intOrder (name : String) (holds : Expr → Expr) : Function where
  name := name
  seen := some asBool
  parameters := ["a1", "a2"]
  body := [
    .call (some "a") "int_limbs" ["a1"],
    .call (some "sign1") "int_sign" ["a1"],
    .call (some "b") "int_limbs" ["a2"],
    .call (some "sign2") "int_sign" ["a2"],
    .callOther (some "order") "rt_big_int_compare" ["sign1", "a", "sign2", "b"],
    .give (holds "order")]

def narrowed (name type : String) (reader : String := "modulo") : Function where
  name := name
  seen := some { result := type, parameters := [object] }
  parameters := ["a"]
  body := [.call (some "value") reader ["a"], .give "value"]

def exported : List Function := [
  { name := "lean_cstr_to_nat"
    about := "A decimal literal. Compiled Lean writes every literal of 2^32 or more this way, each time the literal\nis evaluated. It passes digits and nothing else; anything but digits stops the machine."
    seen := some { result := object, parameters := ["char const *"] }
    parameters := ["digits"]
    body := [
      .branch (Expr.eq (.part 1 "digits") 0) [.stop "lean_cstr_to_nat was given no digits"] [],
      .call (some "array") "array_new" [0],
      .set "at" 0,
      .loop (Expr.ne (.part 1 ("digits" + "at")) 0) [
        .set "digit" (.part 1 ("digits" + "at")),
        .branch (Expr.or (Expr.lt "digit" 48) (Expr.lt 57 "digit"))
          [.stop "lean_cstr_to_nat was given something that is not a digit"] [],
        .callOther (some "array") "rt_big_decimal" ["array", "digit" - 48],
        .set "at" ("at" + 1)],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  { name := "lean_big_usize_to_nat", seen := some { result := object, parameters := ["size_t"] }, parameters := ["n"],
    body := [.call (some "result") "nat_of_word" ["n"], .give "result"] },
  { name := "lean_big_uint64_to_nat", seen := some { result := object, parameters := ["uint64_t"] }, parameters := ["n"],
    body := [.call (some "result") "nat_of_word" ["n"], .give "result"] },
  natOperation "lean_nat_big_add" "rt_big_add" "",
  natOperation "lean_nat_big_sub" "rt_big_sub" "Subtraction of natural numbers stops at zero.",
  natOperation "lean_nat_big_mul" "rt_big_mul" "",
  { name := "lean_nat_overflow_mul"
    about := "The product of two small numbers that does not fit in a tagged word."
    seen := some { result := object, parameters := ["size_t", "size_t"] }
    parameters := ["a1", "a2"]
    body := [
      .call (some "a") "limbs_of_word" ["a1"],
      .call (some "b") "limbs_of_word" ["a2"],
      .callOther (some "array") "rt_big_mul" ["a", "b"],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  natOperation "lean_nat_big_div" "rt_big_div" "In Lean, `n / 0 = 0`.",
  { name := "lean_nat_big_mod"
    about := "In Lean, `n % 0 = n`."
    seen := some two
    parameters := ["a1", "a2"]
    body := [
      .branch (Expr.eq "a2" (box 0)) [.callOther none "lean_inc" ["a1"], .give "a1"] [],
      .call (some "a") "nat_limbs" ["a1"],
      .call (some "b") "nat_limbs" ["a2"],
      .callOther (some "array") "rt_big_mod" ["a", "b"],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  natOrder "lean_nat_big_eq" (Expr.eq · 1),
  natOrder "lean_nat_big_le" (Expr.ne · 2),
  natOrder "lean_nat_big_lt" (Expr.eq · 0),
  natOperation "lean_nat_big_land" "rt_big_and" "",
  natOperation "lean_nat_big_lor" "rt_big_or" "",
  { name := "rt_big_nat_shiftl"
    about := "`a <<< shift`."
    seen := some { result := object, parameters := [object, "size_t"] }
    parameters := ["a1", "shift"]
    body := [
      .call (some "a") "nat_limbs" ["a1"],
      .callOther (some "array") "rt_big_shift_left" ["a", "shift"],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  { name := "lean_nat_big_shiftr"
    about := "`a1 >>> a2` when either is not small."
    seen := some two
    parameters := ["a1", "a2"]
    body := [
      -- A shift of 2^63 or more leaves nothing of any number that fits in memory.
      .branch (isWord "a2") [] [.give (box 0)],
      .set "shift" (unbox "a2"),
      .call (some "a") "nat_limbs" ["a1"],
      -- Lean's runtime shifts by at most 2^32 - 1 bits and refuses a longer shift that would leave something.
      .branch (Expr.lt low32 "shift")
        [.call (some "highest") "log2" ["a"],
         drop "a",
         .branch (Expr.le "shift" "highest") [.outside none "lean_internal_panic(\"Nat.shiftr exponent is too big\")"] [],
         .give (box 0)] [],
      .callOther (some "array") "rt_big_shift_right" ["a", "shift"],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  { name := "rt_big_nat_pow"
    about := "`a ^ exponent`. Anything to the power 0 is 1, zero included."
    seen := some { result := object, parameters := [object, "size_t"] }
    parameters := ["a1", "exponent"]
    body := [
      .call (some "a") "nat_limbs" ["a1"],
      .callOther (some "array") "rt_big_power" ["a", "exponent"],
      .call (some "result") "nat_from" ["array"],
      .give "result"] },
  { name := "rt_big_nat_log2"
    seen := some { result := "size_t", parameters := [object] }
    parameters := ["a1"]
    body := [
      .call (some "a") "nat_limbs" ["a1"],
      .call (some "result") "log2" ["a"],
      drop "a",
      .give "result"] },
  { name := "rt_big_nat_to_size"
    about := "A natural number as a size if it is below 2^64. If it is not, reports \"out of memory\" and stops, as\nLean's runtime does: nothing that large can be the size of anything."
    seen := some { result := "size_t", parameters := [object] }
    parameters := ["a"]
    body := [
      .branch (isWord "a") [.give (unbox "a")] [],
      .call (some "count") "checked" ["a"],
      .branch (Expr.lt 2 "count") [outOfMemory] [],
      .call (some "value") "magnitude_low" ["a"],
      .give "value"] },
  { name := "lean_big_int_to_nat"
    about := "An integer that is known not to be negative, as a natural number. Gives up `a`. Lean's runtime does not\nlook at the sign and would hand back a negative natural number; that cannot be allowed to exist."
    seen := some { result := object, parameters := [object] }
    parameters := ["a"]
    body := [
      .call (some "limbs") "int_limbs" ["a"],
      .call (some "negative") "int_sign" ["a"],
      .branch (Expr.ne "negative" 0) [.stop "a negative integer was turned into a natural number"] [],
      .call (some "result") "nat_from" ["limbs"],
      drop "a",
      .give "result"] },
  { name := "lean_big_size_t_to_int"
    about := "A natural number too large for a small integer, as an integer."
    seen := some { result := object, parameters := ["size_t"] }, parameters := ["n"],
    body := [.call (some "result") "int_of_word" [0, "n"], .give "result"] },
  { name := "lean_big_int64_to_int"
    seen := some { result := object, parameters := ["int64_t"] }, parameters := ["n"],
    body := [
      -- A value with its top bit set is below zero; negated as a word, so the most negative does not overflow.
      .branch (Expr.le (.lit 0x8000000000000000) "n")
        [.call (some "result") "int_of_word" [1, 0 - "n"], .give "result"] [],
      .call (some "result") "int_of_word" [0, "n"],
      .give "result"] },
  { name := "lean_int_big_neg"
    seen := some { result := object, parameters := [object] }
    parameters := ["a"]
    body := [
      .call (some "limbs") "int_limbs" ["a"],
      .call (some "negative") "int_sign" ["a"],
      .call (some "result") "int_result" [1 - "negative", "limbs", sizeOf "limbs"],
      drop "limbs",
      .give "result"] },
  intOperation "lean_int_big_add" "rt_big_int_add" false,
  intOperation "lean_int_big_sub" "rt_big_int_add" true,
  intOperation "lean_int_big_mul" "rt_big_int_mul" false,
  intOperation "lean_int_big_ediv" "rt_big_int_ediv" false
    "`Int.ediv` and `Int.emod`: the division whose remainder is never negative, `n = d * (n / d) + n % d` with\n`0 <= n % d < |d|`, and `n / 0 = 0`, `n % 0 = n`.",
  { name := "lean_int_big_emod"
    seen := some two
    parameters := ["a1", "a2"]
    body := [
      .call (some "d") "int_limbs" ["a2"],
      .branch (Expr.eq (sizeOf "d") 0) [drop "d", .callOther none "lean_inc" ["a1"], .give "a1"] [],
      .call (some "n") "int_limbs" ["a1"],
      .call (some "negative") "int_sign" ["a1"],
      .callOther (some "array") "rt_big_int_emod" ["negative", "n", "d"],
      .call (some "result") "int_from" ["array"],
      .give "result"] },
  intOrder "lean_int_big_eq" (Expr.eq · 1),
  intOrder "lean_int_big_le" (Expr.ne · 2),
  intOrder "lean_int_big_lt" (Expr.eq · 0),
  narrowed "lean_uint8_of_big_nat" "uint8_t",
  narrowed "lean_uint16_of_big_nat" "uint16_t",
  narrowed "lean_uint32_of_big_nat" "uint32_t",
  narrowed "lean_uint64_of_big_nat" "uint64_t",
  -- Lean's runtime reads the lowest word without regard to sign here. The argument is a natural number.
  narrowed "lean_usize_of_big_nat" "size_t" "magnitude_low",
  narrowed "lean_int64_of_big_int" "int64_t",
  narrowed "lean_isize_of_big_int" "ptrdiff_t"]

def limbs : Seen := { result := object, parameters := [object, object] }
def signedLimbs : Seen := { result := object, parameters := ["uint8_t", object, "uint8_t", object] }

def program : Program where
  about := "Numbers too large for a machine word: what they are in memory. Their arithmetic is Runtime/Big.lean."
  preamble := "#include \"big.h\"\n\n_Static_assert(sizeof(size_t) == 8 && sizeof(void *) == 8, \"the number code is written for a 64-bit machine\");\n\n/* Runtime/Big.lean. Each takes the arrays it is given for its own and returns one that is the caller's. */\nlean_object * rt_big_add(lean_object *, lean_object *);\nlean_object * rt_big_sub(lean_object *, lean_object *);\nlean_object * rt_big_mul(lean_object *, lean_object *);\nlean_object * rt_big_div(lean_object *, lean_object *);\nlean_object * rt_big_mod(lean_object *, lean_object *);\nlean_object * rt_big_and(lean_object *, lean_object *);\nlean_object * rt_big_or(lean_object *, lean_object *);\nuint8_t rt_big_compare(lean_object *, lean_object *);\nlean_object * rt_big_decimal(lean_object *, uint32_t);\nlean_object * rt_big_shift_left(lean_object *, size_t);\nlean_object * rt_big_shift_right(lean_object *, size_t);\nlean_object * rt_big_power(lean_object *, size_t);\nlean_object * rt_big_int_add(uint8_t, lean_object *, uint8_t, lean_object *);\nlean_object * rt_big_int_mul(uint8_t, lean_object *, uint8_t, lean_object *);\nlean_object * rt_big_int_ediv(uint8_t, lean_object *, uint8_t, lean_object *);\nlean_object * rt_big_int_emod(uint8_t, lean_object *, lean_object *);\nuint8_t rt_big_int_compare(uint8_t, lean_object *, uint8_t, lean_object *);\n"
  globals := []
  arrays := []
  others := [
    ("lean_alloc_object", { result := object, parameters := ["size_t"] }),
    ("lean_dec", { result := "void", parameters := [object] }),
    ("lean_inc", { result := "void", parameters := [object] }),
    ("rt_big_add", limbs), ("rt_big_sub", limbs), ("rt_big_mul", limbs), ("rt_big_div", limbs),
    ("rt_big_mod", limbs), ("rt_big_and", limbs), ("rt_big_or", limbs),
    ("rt_big_compare", { result := "uint8_t", parameters := [object, object] }),
    ("rt_big_decimal", { result := object, parameters := [object, "uint32_t"] }),
    ("rt_big_shift_left", { result := object, parameters := [object, "size_t"] }),
    ("rt_big_shift_right", { result := object, parameters := [object, "size_t"] }),
    ("rt_big_power", { result := object, parameters := [object, "size_t"] }),
    ("rt_big_int_add", signedLimbs), ("rt_big_int_mul", signedLimbs), ("rt_big_int_ediv", signedLimbs),
    ("rt_big_int_emod", { result := object, parameters := ["uint8_t", object, object] }),
    ("rt_big_int_compare", { result := "uint8_t", parameters := ["uint8_t", object, "uint8_t", object] })]
  functions := [arrayNew, limbsOfWord, checked, limbsOfObject, natLimbs, intSign, intLimbs, trimmed, bigNew,
    natResult, intResult, natFrom, intFrom, natOfWord, intOfWord, log2, magnitudeLow, modulo] ++ exported

end Mini.Number
