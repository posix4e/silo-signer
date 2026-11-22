import Platform

/-! # The big-number test

Puts the runtime's arithmetic on numbers of 2^63 and above (and on integers outside 32 bits) through every
function compiled Lean calls for it, and writes down what came out. Linked once against Lean's own runtime
(`big-test`) and once against the minimal runtime (`big-test-min`); the two outputs must be byte for byte the
same.

Most results are not printed but folded into a running hash, one per group, so that several hundred thousand
of them fit in a few dozen lines. Each group also counts identities that must hold whatever the runtime
(`(a / b) * b + a % b = a` and the like); every such count must be zero.

Nothing here uses a string function beyond turning a literal into bytes, or prints through anything but
`Platform.write`: the minimal runtime has no output streams. It also stays away from the operations whose
runtime functions the minimal runtime does not have because nothing else uses them: `Nat.xor`, `Nat.gcd`,
`Int.tdiv`, `Int.tmod`, and the conversions from `Int` to 8, 16 and 32 bits. -/

namespace BigTest

/-! ## Writing numbers down -/

def hexDigit (d : UInt32) : UInt8 := if d < 10 then (48 + d).toUInt8 else (87 + d).toUInt8

/-- `n` in 32-bit pieces, most significant first; one piece for zero. -/
partial def pieces (n : Nat) (acc : List UInt32 := []) : List UInt32 :=
  if n < 4294967296 then n.toUInt32 :: acc
  else pieces (n / 4294967296) ((n % 4294967296).toUInt32 :: acc)

/-- `n` in hexadecimal, at least one digit. -/
def hexNat (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut started := false
  for piece in pieces n do
    for i in [0:8] do
      let digit := (piece >>> (28 - 4 * i).toUInt32) &&& 0xF
      if started || digit != 0 then
        out := out.push (hexDigit digit)
        started := true
  return if started then out else out.push 48

def hexInt (i : Int) : ByteArray :=
  if i < 0 then (ByteArray.empty.push 45) ++ hexNat i.natAbs else hexNat i.natAbs

/-- All sixteen hexadecimal digits of a word, without going through `Nat`. -/
def hexWord (x : UInt64) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [0:16] do
    out := out.push (hexDigit ((x >>> (60 - 4 * i).toUInt64) &&& 0xF).toUInt32)
  return out

partial def decimalDigits (n : Nat) (acc : List UInt8 := []) : List UInt8 :=
  if n < 10 then (48 + n).toUInt8 :: acc else decimalDigits (n / 10) ((48 + n % 10).toUInt8 :: acc)

/-- A small number in decimal. -/
def decimal (n : Nat) : ByteArray := (decimalDigits n).foldl ByteArray.push ByteArray.empty

def line (name : String) (value : ByteArray) : ByteArray :=
  name.toUTF8 ++ ": ".toUTF8 ++ value ++ "\n".toUTF8

def natLine (name : String) (n : Nat) : ByteArray := line name (hexNat n)

def intLine (name : String) (i : Int) : ByteArray := line name (hexInt i)

/-! ## A group of results -/

/-- The results of one group: their number, a hash of all of them in order (64-bit FNV-1a over 32-bit pieces
and markers), and how many identities did not hold. -/
structure Tally where
  hash : UInt64 := 0xcbf29ce484222325
  count : Nat := 0
  failed : Nat := 0

namespace Tally

def mix (t : Tally) (x : UInt64) : Tally := { t with hash := (t.hash ^^^ x) * 0x100000001b3 }

def counted (t : Tally) : Tally := { t with count := t.count + 1 }

/-- Markers are above 32 bits, so no piece of a number can be taken for one. -/
def nat (t : Tally) (n : Nat) : Tally :=
  (((pieces n).foldl (fun t piece => t.mix piece.toUInt64) t).mix 0x100000000).counted

def int (t : Tally) (i : Int) : Tally :=
  (t.mix (if i < 0 then 0x200000000 else 0x300000000)).nat i.natAbs

def bool (t : Tally) (b : Bool) : Tally := (t.mix (if b then 0x400000001 else 0x400000000)).counted

def word (t : Tally) (x : UInt64) : Tally := ((t.mix (x >>> 32)).mix (x &&& 0xFFFFFFFF)).mix 0x500000000 |>.counted

def bytes (t : Tally) (b : ByteArray) : Tally :=
  ((b.foldl (fun t x => t.mix x.toUInt64) t).mix 0x600000000).counted

/-- An identity that has to hold on any runtime. -/
def must (t : Tally) (holds : Bool) : Tally := if holds then t else { t with failed := t.failed + 1 }

def line (t : Tally) (name : String) : ByteArray :=
  BigTest.line name (decimal t.count ++ " results, hash ".toUTF8 ++ hexWord t.hash ++ ", ".toUTF8
    ++ decimal t.failed ++ " identities failed".toUTF8)

end Tally

/-! ## Numbers to try

Pseudo-random, from a linear congruential generator with a fixed seed, so every run is the same run. -/

abbrev Gen := StateM UInt64

def next : Gen UInt32 := modifyGet fun (state : UInt64) =>
  let state := state * 6364136223846793005 + 1442695040888963407
  ((state >>> 32).toUInt32, state)

def below (n : Nat) : Gen Nat := do return (← next).toNat % n

def word : Gen UInt64 := do return ((← next).toUInt64 <<< 32) ||| (← next).toUInt64

/-- One 32-bit limb. Half the time it is one of the values at which carries, borrows and the guesses of long
division go wrong; uniformly random limbs would almost never reach those. -/
def limb : Gen Nat := do
  match (← below 16) with
  | 0 => return 0
  | 1 => return 1
  | 2 => return 0xFFFFFFFF
  | 3 => return 0x80000000
  | 4 => return 0x7FFFFFFF
  | 5 => return 0xFFFFFFFE
  | 6 => return 0x80000001
  | 7 => return 2
  | _ => return (← next).toNat

/-- A natural number of exactly `count` limbs or fewer (the top ones may come out zero), built the way
schoolbook notation reads: by multiplying up and adding, or by shifting and or-ing. -/
def natOf (count : Nat) : Gen Nat := do
  let shifting := (← below 2) == 0
  let mut n := 0
  for _ in [0:count] do
    let l ← limb
    n := if shifting then (n <<< 32) ||| l else n * 4294967296 + l
  return n

/-- A natural number of up to `maxLimbs` limbs: sometimes zero, sometimes small, usually big. -/
def nat (maxLimbs : Nat) : Gen Nat := do natOf (← below (maxLimbs + 1))

def int (maxLimbs : Nat) : Gen Int := do
  let n ← nat maxLimbs
  return if (← below 2) == 0 then (n : Int) else -(n : Int)

def run (seed : UInt64) (group : Gen Tally) : Tally := (Id.run (group.run seed)).1

/-! ## Numbers at the edges -/

/-- Around every power of two where a representation changes: 2^31 and 2^32 (small integers, one limb), 2^63
and 2^64 (small natural numbers, one word), and whole numbers of limbs beyond. -/
def natEdges : List Nat := Id.run do
  let mut out : List Nat := [0, 1, 2, 3, 10, 0xFFFF, 0x10000]
  for k in [31, 32, 33, 62, 63, 64, 65, 95, 96, 127, 128, 129, 255, 256, 257, 511, 512, 1024] do
    let p := 2 ^ k
    out := out ++ [p - 1, p, p + 1]
  return out ++ [
    6364136223846793005,
    10000000000000000000,
    1000000000000000000000000000000,
    115792089237316195423570985008687907852837564279074904382605163141518161494337,
    115792089237316195423570985008687907853269984665640564039457584007908834671663]

def intEdges : List Int := Id.run do
  let mut out : List Int := [0]
  for k in [1, 31, 32, 33, 63, 64, 65, 127, 128, 256] do
    let p : Nat := 2 ^ k
    for n in [p - 1, p, p + 1] do
      out := out ++ [(n : Int), -(n : Int)]
  return out

/-! ## Literals

A literal of 2^32 or more reaches the runtime as its decimal digits. -/

def literals : ByteArray :=
  natLine "literal 2^32" 4294967296
  ++ natLine "literal 2^63 - 1" 9223372036854775807
  ++ natLine "literal 2^63" 9223372036854775808
  ++ natLine "literal 2^64 - 1" 18446744073709551615
  ++ natLine "literal 2^64" 18446744073709551616
  ++ natLine "literal 2^127" 170141183460469231731687303715884105728
  ++ natLine "literal 2^128 - 1" 340282366920938463463374607431768211455
  ++ natLine "literal 2^128" 340282366920938463463374607431768211456
  ++ natLine "literal 2^256" 115792089237316195423570985008687907853269984665640564039457584007913129639936
  ++ natLine "literal 10^19" 10000000000000000000
  ++ natLine "literal 10^30" 1000000000000000000000000000000
  ++ natLine "literal 10^100"
      10000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
  ++ natLine "literal 2^521 - 1"
      6864797660130609714981900799081393217269435300143305409394463459185543183397656052122559640661454554977296311391480858037121987999716643812574028291115057151
  ++ intLine "literal -2^31" (-2147483648)
  ++ intLine "literal -2^31 - 1" (-2147483649)
  ++ intLine "literal -2^63" (-9223372036854775808)
  ++ intLine "literal -2^64" (-18446744073709551616)
  ++ intLine "literal -10^30" (-1000000000000000000000000000000)

/-! ## Natural numbers at the edges -/

def natPairs : Tally := Id.run do
  let mut t : Tally := {}
  for a in natEdges do
    for b in natEdges do
      t := t.nat (a + b) |>.nat (a - b) |>.nat (a * b) |>.nat (a / b) |>.nat (a % b)
      t := t.bool (a == b) |>.bool (decide (a ≤ b)) |>.bool (decide (a < b))
      t := t.nat (a &&& b) |>.nat (a ||| b) |>.nat (a >>> b)
      t := t.must ((a + b) - b == a) |>.must ((a ||| b) + (a &&& b) == a + b)
      t := t.must (decide (a ≤ b) == (a - b == 0)) |>.must (decide (a < b) == !decide (b ≤ a))
      if b != 0 then
        t := t.must ((a / b) * b + a % b == a) |>.must (decide (a % b < b)) |>.must ((a * b) / b == a)
      else
        t := t.must (a / b == 0) |>.must (a % b == a)
  return t

def natShifts : Tally := Id.run do
  let mut t : Tally := {}
  for a in natEdges do
    t := t.nat a.log2
    for s in [0, 1, 2, 30, 31, 32, 33, 62, 63, 64, 65, 96, 127, 128, 1000] do
      t := t.nat (a <<< s) |>.nat (a >>> s)
      t := t.must ((a <<< s) >>> s == a) |>.must (a <<< s == a * 2 ^ s) |>.must (a >>> s == a / 2 ^ s)
      if a != 0 then t := t.must ((a <<< s).log2 == a.log2 + s)
  return t

def natPowers : Tally := Id.run do
  let mut t : Tally := {}
  for a in natEdges do
    let mut product := 1
    for e in [0:8] do
      t := t.nat (a ^ e) |>.must (a ^ e == product)
      product := product * a
  -- Zero and one to a power too large to be an exponent, and zero shifted that far, are still answered.
  for huge in natEdges do
    for small in natEdges.take 2 do
      t := t.nat (small ^ huge)
    for nothing in natEdges.take 1 do
      t := t.nat (nothing <<< huge)
  return t

def natWords : Tally := Id.run do
  let mut t : Tally := {}
  for a in natEdges do
    t := t.word a.toUInt8.toUInt64 |>.word a.toUInt16.toUInt64 |>.word a.toUInt32.toUInt64
    t := t.word a.toUInt64 |>.word a.toUSize.toUInt64 |>.word a.toInt64.toUInt64 |>.word a.toISize.toUSize.toUInt64
    t := t.nat a.toUInt64.toNat |>.nat a.toUSize.toNat
    t := t.must (a.toUInt64.toNat == a % 18446744073709551616) |>.must (a.toUSize.toNat == a % 18446744073709551616)
    t := t.must (a.toUInt32.toNat == a % 4294967296) |>.must (a.toUInt16.toNat == a % 65536)
    t := t.must (a.toUInt8.toNat == a % 256) |>.must (a.toInt64.toUInt64 == a.toUInt64)
  return t

/-- Offsets and lengths from 2^63 to 2^64 - 1: numbers the runtime has to read out of an object to find that
they are past the end of everything. (From 2^64 on, Lean's runtime gives up with "out of memory".) -/
def natSizes : Tally := Id.run do
  let mut t : Tally := {}
  let source := ByteArray.empty.push 1 |>.push 2 |>.push 3 |>.push 4 |>.push 5
  let target := ByteArray.empty.push 9 |>.push 8 |>.push 7
  for n in natEdges do
    if decide (9223372036854775808 ≤ n) && decide (n < 18446744073709551616) then
      -- From past the end of the source: nothing is copied.
      t := t.bytes (source.copySlice n target 0 2)
      -- To past the end of the target: appended. More than there is: all there is.
      t := t.bytes (source.copySlice 1 target n 2) |>.bytes (source.copySlice 1 target 1 n)
      t := t.bytes (source.copySlice 0 target n n)
  return t

/-! ## Integers at the edges -/

def intPairs : Tally := Id.run do
  let mut t : Tally := {}
  for a in intEdges do
    for b in intEdges do
      t := t.int (a + b) |>.int (a - b) |>.int (a * b) |>.int (a / b) |>.int (a % b)
      t := t.bool (a == b) |>.bool (decide (a ≤ b)) |>.bool (decide (a < b))
      t := t.must ((a + b) - b == a) |>.must (a - b == a + -b) |>.must (decide (a < b) == !decide (b ≤ a))
      if b != 0 then
        t := t.must (b * (a / b) + a % b == a) |>.must (decide (0 ≤ a % b))
        t := t.must (decide ((a % b).toNat < b.natAbs)) |>.must ((a * b) / b == a)
      else
        t := t.must (a / b == 0) |>.must (a % b == a)
  return t

def intSingles : Tally := Id.run do
  let mut t : Tally := {}
  for a in intEdges do
    t := t.int (-a) |>.nat a.natAbs |>.nat a.toNat
    t := t.word a.toInt64.toUInt64 |>.word a.toISize.toUSize.toUInt64
    t := t.int a.toInt64.toInt |>.int a.toISize.toInt
    t := t.must (- -a == a) |>.must (a + -a == 0) |>.must ((a.natAbs : Int) == if a < 0 then -a else a)
    t := t.must ((a.toNat : Int) == if a < 0 then 0 else a)
    t := t.must ((a.toInt64.toInt - a) % 18446744073709551616 == 0)
    t := t.must (a.toISize.toInt == a.toInt64.toInt)
  -- Small natural numbers that are not small integers, and sums of small integers that are not small.
  for n in natEdges do
    t := t.int (n : Int) |>.int (-(n : Int)) |>.must (((n : Int)).toNat == n) |>.must ((-(n : Int)).natAbs == n)
  for a in intEdges.take 13 do
    for b in intEdges.take 13 do
      t := t.int (a + b) |>.int (a - b) |>.int (a * b)
  return t

/-! ## Long division, case by case

Dividend and divisor as 32-bit limbs, most significant first. The first cases are the ones Hacker's Delight
tests Knuth's algorithm D with, widened to 32-bit limbs: among them are quotient guesses that come out as
2^32 and 2^32 + 1, guesses one and two too large, and the rare one that is only found out by a subtraction
going below zero. -/

def fromLimbs (limbs : List Nat) : Nat := limbs.foldl (fun n l => n * 4294967296 + l) 0

def divisionCases : List (List Nat × List Nat) := [
  ([3], [2]), ([3], [3]), ([3], [4]), ([3], [0xFFFFFFFF]), ([0xFFFFFFFF], [1]), ([0xFFFFFFFF], [0xFFFFFFFF]),
  ([0xFFFFFFFF], [3]), ([0xFFFFFFFF, 0xFFFFFFFF], [1]), ([0xFFFFFFFF, 0xFFFFFFFF], [0xFFFFFFFF]),
  ([0xFFFFFFFE, 0xFFFFFFFF], [0xFFFFFFFF]), ([0x00001234, 0x00005678], [0x00009ABC]),
  ([0, 0], [1, 0]), ([7, 0], [3, 0]), ([7, 5], [3, 0]), ([6, 0], [2, 0]),
  ([0x80000000], [0x40000001]), ([0x80000000, 0], [0x40000001]), ([0x80000000, 0], [0x40000000, 1]),
  ([0x0000BCDE, 0x0000789A], [0x0000BCDE, 0x0000789A]), ([0x0000BCDE, 0x0000789B], [0x0000BCDE, 0x0000789A]),
  ([0x0000BCDE, 0x00007899], [0x0000BCDE, 0x0000789A]), ([0x0000FFFF, 0x0000FFFF], [0x0000FFFF, 0x0000FFFF]),
  ([0x0000FFFF, 0x0000FFFF], [1, 0]), ([0x00000123, 0x00004567, 0x000089AB], [1, 0]),
  ([0x80000000, 0xFFFFFFFE, 0], [0x80000000, 0xFFFFFFFF]),
  ([0x80000000, 0, 3], [0x20000000, 0, 1]),
  ([0x7FFFFFFF, 0x80000000, 0, 0], [0x80000000, 0, 1]),
  ([0x80000000, 0, 0xFFFFFFFE, 0], [0x80000000, 0, 0xFFFFFFFF]),
  ([0x80000000, 0, 0, 0], [0x80000000, 0, 1]),
  ([0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], [0xFFFFFFFF, 0xFFFFFFFF]),
  ([0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], [0x80000000, 0]),
  ([0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], [1, 0]),
  ([0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF], [1, 0, 0, 0, 0]),
  ([1, 0, 0, 0, 0, 0, 0, 0], [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF]),
  ([1, 0, 0, 0, 0, 0, 0, 0], [1, 0xFFFFFFFF, 0xFFFFFFFF]),
  ([0x7FFFFFFF, 0xFFFFFFFF, 0, 0, 0], [0x80000000, 0, 0]),
  ([0x12345678, 0x9ABCDEF0, 0x0FEDCBA9, 0x87654321, 0xDEADBEEF], [0x00000001, 0x00000000, 0x00000001]),
  ([0x12345678, 0x9ABCDEF0, 0x0FEDCBA9, 0x87654321, 0xDEADBEEF], [0x00010000, 0x00000000]),
  ([0x12345678, 0x9ABCDEF0, 0x0FEDCBA9, 0x87654321, 0xDEADBEEF], [0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFE])]

def divisions : ByteArray × Tally := Id.run do
  let mut out := ByteArray.empty
  let mut t : Tally := {}
  let mut index := 0
  for (dividend, divisor) in divisionCases do
    let a := fromLimbs dividend
    let b := fromLimbs divisor
    let q := a / b
    let r := a % b
    t := t.nat q |>.nat r |>.must (q * b + r == a) |>.must (decide (r < b))
    -- The same division with every combination of signs.
    for (x, y) in [((a : Int), (b : Int)), (-(a : Int), (b : Int)), ((a : Int), -(b : Int)), (-(a : Int), -(b : Int))] do
      t := t.int (x / y) |>.int (x % y) |>.must (y * (x / y) + x % y == x) |>.must (decide (0 ≤ x % y))
    out := out ++ "division ".toUTF8 ++ decimal index ++ ": ".toUTF8 ++ hexNat a ++ " / ".toUTF8 ++ hexNat b
      ++ " = ".toUTF8 ++ hexNat q ++ " rest ".toUTF8 ++ hexNat r ++ "\n".toUTF8
    index := index + 1
  return (out, t)

/-! ## Pseudo-random numbers -/

def randomNats (rounds : Nat) : Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:rounds] do
    let a ← nat 12
    let b ← nat 12
    t := t.nat (a + b) |>.nat (a - b) |>.nat (b - a) |>.nat (a * b)
    t := t.nat (a / b) |>.nat (a % b) |>.nat (b / a) |>.nat (b % a)
    t := t.bool (a == b) |>.bool (decide (a ≤ b)) |>.bool (decide (a < b))
    t := t.nat (a &&& b) |>.nat (a ||| b)
    t := t.must ((a + b) - b == a) |>.must ((a ||| b) + (a &&& b) == a + b) |>.must (a * b == b * a)
    t := t.must (decide (a ≤ b) == (a - b == 0)) |>.must (decide (a < b) == !decide (b ≤ a))
    if b != 0 then
      t := t.must ((a / b) * b + a % b == a) |>.must (decide (a % b < b)) |>.must ((a * b) / b == a)
      t := t.must ((a * b) % b == 0)
  return t

/-- Division where the answer is known beforehand: the dividend is made from a quotient, a divisor and a
remainder, and dividing has to give the first and the last back. -/
def randomDivisions (rounds : Nat) : Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:rounds] do
    let q ← nat 10
    let b ← natOf (1 + (← below 8))
    let b := if b == 0 then 1 else b
    let r := (← nat 8) % b
    let a := q * b + r
    t := t.nat a |>.nat (a / b) |>.nat (a % b) |>.must (a / b == q) |>.must (a % b == r)
    -- A long dividend over a short divisor, and numbers of nearly the same length.
    let long ← natOf (20 + (← below 20))
    let short ← natOf (1 + (← below 5))
    let short := if short == 0 then 3 else short
    t := t.nat (long / short) |>.nat (long % short)
    t := t.must ((long / short) * short + long % short == long) |>.must (decide (long % short < short))
    let near := b + (← nat 1)
    t := t.nat (a / near) |>.nat (a % near) |>.nat (near / b) |>.nat (near % b)
    t := t.must ((a / near) * near + a % near == a)
  return t

def randomShifts (rounds : Nat) : Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:rounds] do
    let a ← nat 8
    let s ← below 200
    t := t.nat (a <<< s) |>.nat (a >>> s) |>.nat a.log2
    t := t.must ((a <<< s) >>> s == a) |>.must (a <<< s == a * 2 ^ s) |>.must (a >>> s == a / 2 ^ s)
    t := t.must (((a >>> s) <<< s) + a % 2 ^ s == a)
    if a != 0 then t := t.must (decide (2 ^ a.log2 ≤ a)) |>.must (decide (a < 2 ^ (a.log2 + 1)))
    -- Powers, checked against multiplying one factor at a time.
    let base ← nat 3
    let exponent ← below 12
    let mut product := 1
    for _ in [0:exponent] do
      product := product * base
    t := t.nat (base ^ exponent) |>.must (base ^ exponent == product)
  return t

def randomInts (rounds : Nat) : Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:rounds] do
    let a ← int 6
    let b ← int 6
    t := t.int (a + b) |>.int (a - b) |>.int (a * b) |>.int (a / b) |>.int (a % b) |>.int (-a)
    t := t.bool (a == b) |>.bool (decide (a ≤ b)) |>.bool (decide (a < b))
    t := t.nat a.natAbs |>.nat b.toNat
    t := t.must ((a + b) - b == a) |>.must (a - b == a + -b) |>.must (a * b == b * a)
    t := t.must (decide (a < b) == !decide (b ≤ a)) |>.must (decide (a ≤ b) == decide (0 ≤ b - a))
    if b != 0 then
      t := t.must (b * (a / b) + a % b == a) |>.must (decide (0 ≤ a % b))
      t := t.must (decide ((a % b).toNat < b.natAbs)) |>.must ((a * b) / b == a) |>.must ((a * b) % b == 0)
  return t

def randomWords (rounds : Nat) : Gen Tally := do
  let mut t : Tally := {}
  for _ in [0:rounds] do
    let n ← nat 4
    t := t.word n.toUInt8.toUInt64 |>.word n.toUInt16.toUInt64 |>.word n.toUInt32.toUInt64
    t := t.word n.toUInt64 |>.word n.toUSize.toUInt64 |>.word n.toInt64.toUInt64
    t := t.must (n.toUInt64.toNat == n % 18446744073709551616) |>.must (n.toUSize.toNat == n % 18446744073709551616)
    t := t.must (n.toUInt32.toNat == n % 4294967296) |>.must (n.toUInt8.toNat == n % 256)
    -- Words as natural numbers: half of them are 2^63 or more, and most products do not fit a word.
    let x ← word
    let y ← word
    t := t.nat x.toNat |>.nat x.toUSize.toNat |>.nat (x.toNat * y.toNat) |>.nat (x.toNat + y.toNat)
    t := t.must (x.toNat.toUInt64 == x) |>.must ((x.toNat * y.toNat).toUInt64 == x * y)
    t := t.must ((x.toNat + y.toNat).toUInt64 == x + y) |>.must (x.toUSize.toNat.toUSize == x.toUSize)
    let half := (x >>> 1).toNat
    let other := (y >>> 1).toNat
    t := t.nat (half * other) |>.nat (half + other) |>.must ((half * other).toUInt64 == (x >>> 1) * (y >>> 1))
    -- Integers into 64 bits and back.
    let i ← int 3
    t := t.word i.toInt64.toUInt64 |>.word i.toISize.toUSize.toUInt64 |>.int i.toInt64.toInt |>.int i.toISize.toInt
    t := t.must ((i.toInt64.toInt - i) % 18446744073709551616 == 0)
    t := t.must (x.toInt64.toInt.toInt64 == x.toInt64) |>.int x.toInt64.toInt |>.int x.toUSize.toISize.toInt
    t := t.must (decide (-9223372036854775808 ≤ x.toInt64.toInt)) |>.must (decide (x.toInt64.toInt < 9223372036854775808))
  return t

/-- Runs the whole test and prints its lines. The status is 0 if every identity held. -/
def report : IO UInt32 := do
  Platform.write literals
  let edges := [(natPairs, "natural numbers at the edges, in pairs"), (natShifts, "shifts and log2 at the edges"),
    (natPowers, "powers at the edges"), (natWords, "natural numbers into fixed widths"),
    (natSizes, "natural numbers of 2^63 and more as sizes"),
    (intPairs, "integers at the edges, in pairs"), (intSingles, "integers at the edges, one at a time")]
  let (divisionLines, divisionTally) := divisions
  Platform.write divisionLines
  let random := [(run 1 (randomNats 3000), "pseudo-random natural numbers"),
    (run 2 (randomDivisions 2000), "pseudo-random divisions"), (run 3 (randomShifts 2000), "pseudo-random shifts and powers"),
    (run 4 (randomInts 3000), "pseudo-random integers"), (run 5 (randomWords 2000), "pseudo-random fixed widths")]
  let mut results := 0
  let mut failed := 0
  for (tally, name) in edges ++ [(divisionTally, "long division, case by case")] ++ random do
    Platform.write (tally.line name)
    results := results + tally.count
    failed := failed + tally.failed
  Platform.write (line "total" (decimal results ++ " results, ".toUTF8 ++ decimal failed ++ " identities failed".toUTF8))
  return if failed == 0 then 0 else 1

end BigTest
