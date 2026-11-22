/-! # Arithmetic on numbers too large for a machine word

Compiled Lean keeps a natural number below 2^63 in a tagged word and does the arithmetic inline. For
anything larger it calls the runtime. This is that arithmetic: `Mini/Number.lean` knows how such a number is laid
out in memory and what a result has to look like, and hands the limbs here for everything else.

A number is its limbs, 32 bits each, least significant first. A limb is widened to 64 bits to be worked on,
so nothing here overflows a machine word and nothing here is itself a big number: this file is what a big
number's arithmetic is made of, so it cannot use one. Indices and sizes are small.

It also runs before any module has been initialised, since initialising Lean's own library evaluates big
literals. So nothing here may be a constant that is built at start-up: `compiler.extract_closed` is off for
the file, and CI checks that its initialiser has nothing to do.

How long an operation takes depends on the numbers. Arithmetic on a secret done through `Nat` or `Int` is
not hidden from someone who can time it.

Every index is checked: reading past the end of a number gives zero, and writing past it does nothing. -/

set_option compiler.extract_closed false

namespace Runtime.Big

abbrev Limbs := Array UInt32

/-- Limb `i`, widened; zero beyond the end. -/
@[inline] def limb (a : Limbs) (i : Nat) : UInt64 := (a.getD i 0).toUInt64

/-- A limb with this value. A limb written as a literal where an array wants an element becomes a constant
that is built when the module is initialised, which is too late (see above); one that comes out of a call
does not. -/
@[noinline] def low (x : UInt64) : UInt32 := x.toUInt32

/-- `n` limbs of zero. -/
def zeros (n : Nat) : Limbs := Array.replicate n (low 0)

/-- The number one. -/
def one (_ : Unit) : Limbs := (Array.mkEmpty 1).push (low 1)

/-- Without the zero limbs at the top. -/
def trim (a : Limbs) : Limbs :=
  if a.size = 0 then a else if a.getD (a.size - 1) 0 == 0 then trim a.pop else a
termination_by a.size
decreasing_by simp [Array.size_pop]; omega

def compareFrom (a b : Limbs) : Nat → UInt8
  | 0 => 1
  | i + 1 => if limb a i < limb b i then 0 else if limb b i < limb a i then 2 else compareFrom a b i

/-- 0 if `a` is smaller than `b`, 1 if they are equal, 2 if it is larger. Neither has a zero limb on top. -/
@[export rt_big_compare]
def compare (a b : Limbs) : UInt8 :=
  if a.size < b.size then 0 else if b.size < a.size then 2 else compareFrom a b a.size

def addLoop (a b : Limbs) (n i : Nat) (carry : UInt64) (r : Limbs) : Limbs :=
  if i < n then
    let t := limb a i + limb b i + carry
    addLoop a b n (i + 1) (t >>> 32) (r.push t.toUInt32)
  else r.push carry.toUInt32
termination_by n - i

@[export rt_big_add]
def add (a b : Limbs) : Limbs :=
  let n := if a.size < b.size then b.size else a.size
  addLoop a b n 0 0 (Array.mkEmpty (n + 1))

/- The difference of two limbs and a borrow is at least -2^32, so as a 64-bit word its top bit says whether
it went below zero. -/
def subLoop (a b : Limbs) (i : Nat) (borrow : UInt64) (r : Limbs) : Limbs :=
  if i < a.size then
    let t := limb a i - limb b i - borrow
    subLoop a b (i + 1) (t >>> 63) (r.push t.toUInt32)
  else r
termination_by a.size - i

/-- `a - b`, for `a` at least `b`. -/
def sub (a b : Limbs) : Limbs := subLoop a b 0 0 (Array.mkEmpty a.size)

/-- Subtraction of natural numbers stops at zero. -/
@[export rt_big_sub]
def natSub (a b : Limbs) : Limbs := if compare a b == 2 then sub a b else Array.mkEmpty 0

/- `r` gains `a * x` from limb `i` up. The step is at most (2^32 - 1)^2 + 2 (2^32 - 1), which fits. -/
def mulRow (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs) : Limbs :=
  if j < a.size then
    let t := limb a j * x + limb r (i + j) + carry
    mulRow a x i (j + 1) (t >>> 32) (r.setIfInBounds (i + j) t.toUInt32)
  else r.setIfInBounds (i + a.size) carry.toUInt32
termination_by a.size - j

def mulLoop (a b : Limbs) (i : Nat) (r : Limbs) : Limbs :=
  if i < b.size then mulLoop a b (i + 1) (mulRow a (limb b i) i 0 0 r) else r
termination_by b.size - i

@[export rt_big_mul]
def mul (a b : Limbs) : Limbs := mulLoop a b 0 (zeros (a.size + b.size))

def scaleLoop (a : Limbs) (m : UInt64) (i : Nat) (carry : UInt64) (r : Limbs) : Limbs :=
  if i < a.size then
    let t := limb a i * m + carry
    scaleLoop a m (i + 1) (t >>> 32) (r.push t.toUInt32)
  else r.push carry.toUInt32
termination_by a.size - i

/-- `a * 10 + digit`: one more digit of a decimal literal. -/
@[export rt_big_decimal]
def decimal (a : Limbs) (digit : UInt32) : Limbs :=
  trim (scaleLoop a 10 0 digit.toUInt64 (Array.mkEmpty (a.size + 1)))

def shiftLeftLoop (a : Limbs) (bits : UInt64) (i : Nat) (carry : UInt64) (r : Limbs) : Limbs :=
  if i < a.size then
    let t := (limb a i <<< bits) ||| carry
    shiftLeftLoop a bits (i + 1) (t >>> 32) (r.push t.toUInt32)
  else r.push carry.toUInt32
termination_by a.size - i

/-- `a` moved up by `whole` limbs and `bits` bits, `bits` below 32: one limb longer than that needs. -/
def shiftLeft (a : Limbs) (whole : Nat) (bits : UInt64) : Limbs :=
  shiftLeftLoop a bits 0 0 (zeros whole)

@[export rt_big_shift_left]
def shiftLeftBy (a : Limbs) (shift : USize) : Limbs := shiftLeft a (shift / 32).toNat (shift % 32).toUInt64

def shiftRightLoop (a : Limbs) (bits : UInt64) (n i : Nat) (r : Limbs) : Limbs :=
  if i < n then
    let t := ((limb a (i + 1) <<< 32) ||| limb a i) >>> bits
    shiftRightLoop a bits n (i + 1) (r.push t.toUInt32)
  else r
termination_by n - i

/-- The limbs of `a` from `whole` up to `n`, moved down by `bits` bits, `bits` below 32. -/
def shiftRight (a : Limbs) (whole n : Nat) (bits : UInt64) : Limbs :=
  shiftRightLoop a bits n whole (Array.mkEmpty (n - whole))

@[export rt_big_shift_right]
def shiftRightBy (a : Limbs) (shift : USize) : Limbs :=
  shiftRight a (shift / 32).toNat a.size (shift % 32).toUInt64

def bitsLoop (a b : Limbs) (either : Bool) (n i : Nat) (r : Limbs) : Limbs :=
  if i < n then
    let x := if either then a.getD i 0 ||| b.getD i 0 else a.getD i 0 &&& b.getD i 0
    bitsLoop a b either n (i + 1) (r.push x)
  else r
termination_by n - i

@[export rt_big_and]
def and (a b : Limbs) : Limbs :=
  let n := if a.size < b.size then a.size else b.size
  bitsLoop a b false n 0 (Array.mkEmpty n)

@[export rt_big_or]
def or (a b : Limbs) : Limbs :=
  let n := if a.size < b.size then b.size else a.size
  bitsLoop a b true n 0 (Array.mkEmpty n)

/-! ## Division -/

/- Division by a single limb, a digit at a time from the top, as on paper. `rest` is below the divisor, so
each step's quotient fits a limb. -/
def divideSmallLoop (a : Limbs) (d : UInt64) (rest : UInt64) (q : Limbs) : Nat → Limbs × Limbs
  | 0 => (q, (Array.mkEmpty 1).push rest.toUInt32)
  | i + 1 =>
    let part := (rest <<< 32) ||| limb a i
    divideSmallLoop a d (part % d) (q.setIfInBounds i (part / d).toUInt32) i

/- How far to shift a limb, which is not zero, for its top bit to be set. -/
def topShift (top : UInt64) (s : UInt64) : Nat → UInt64
  | 0 => s
  | fuel + 1 => if (top <<< s) &&& 0x80000000 == 0 then topShift top (s + 1) fuel else s

/- Knuth's step D3. The guess from the top limbs can be 2^32 or 2^32 + 1, which no limb holds, so that is
corrected first; it is below 2^32 before it is multiplied. A look at one more limb of each catches nearly
every overestimate. Twice round is the most it takes, since `rest` passes 2^32 by then. -/
def refine (guess rest v1 v2 u2 : UInt64) : Nat → UInt64
  | 0 => guess
  | fuel + 1 =>
    if guess > 0xFFFFFFFF || guess * v2 > ((rest <<< 32) ||| u2) then
      let rest := rest + v1
      if rest > 0xFFFFFFFF then guess - 1 else refine (guess - 1) rest v1 v2 u2 fuel
    else guess

/- D4: take `guess * v` off the limbs of `u` from `j` up. Says whether that went below zero. -/
def takeLoop (v : Limbs) (guess : UInt64) (j i : Nat) (carry borrow : UInt64) (u : Limbs) : Limbs × UInt64 :=
  if i < v.size then
    let product := guess * limb v i + carry
    let difference := limb u (i + j) - (product &&& 0xFFFFFFFF) - borrow
    takeLoop v guess j (i + 1) (product >>> 32) (difference >>> 63) (u.setIfInBounds (i + j) difference.toUInt32)
  else
    let difference := limb u (j + v.size) - carry - borrow
    (u.setIfInBounds (j + v.size) difference.toUInt32, difference >>> 63)
termination_by v.size - i

/- D6: the guess was one too large. Put `v` back; the carry out of the top cancels the borrow. -/
def putBackLoop (v : Limbs) (j i : Nat) (carry : UInt64) (u : Limbs) : Limbs :=
  if i < v.size then
    let sum := limb u (i + j) + limb v i + carry
    putBackLoop v j (i + 1) (sum >>> 32) (u.setIfInBounds (i + j) sum.toUInt32)
  else u.setIfInBounds (j + v.size) (limb u (j + v.size) + carry).toUInt32
termination_by v.size - i

/- D2 to D7: one quotient limb at a time, from the top. -/
def divideLongLoop (v : Limbs) (u q : Limbs) : Nat → Limbs × Limbs
  | 0 => (q, u)
  | j + 1 =>
    let n := v.size
    let v1 := limb v (n - 1)
    let top := (limb u (j + n) <<< 32) ||| limb u (j + n - 1)
    let guess := refine (top / v1) (top % v1) v1 (limb v (n - 2)) (limb u (j + n - 2)) 4
    let (u, below) := takeLoop v guess j 0 0 0 u
    if below != 0 then divideLongLoop v (putBackLoop v j 0 0 u) (q.setIfInBounds j (guess - 1).toUInt32) j
    else divideLongLoop v u (q.setIfInBounds j guess.toUInt32) j

/- Long division by two or more limbs: Knuth's algorithm D (The Art of Computer Programming, volume 2,
section 4.3.1). `a` has at least as many limbs as `b`. Both are shifted so that the divisor's top bit is set;
then each guess at a quotient limb is never too small and at most two too large. -/
def divideLong (a b : Limbs) : Limbs × Limbs :=
  let n := b.size
  let s := topShift (limb b (n - 1)) 0 32
  let v := (shiftLeft b 0 s).pop
  let (q, u) := divideLongLoop v (shiftLeft a 0 s) (zeros (a.size - n + 1)) (a.size - n + 1)
  (q, shiftRight u 0 n s)

/-- The quotient rounded down and the remainder, for `b` other than zero with no zero limb on top. Either
may come back with zero limbs on top; whoever makes a number of them takes those off. -/
def divide (a b : Limbs) : Limbs × Limbs :=
  if a.size < b.size then (Array.mkEmpty 0, a)
  else if b.size == 1 then divideSmallLoop a (limb b 0) 0 (zeros a.size) a.size
  else divideLong a b

/-- In Lean, `n / 0 = 0`. -/
@[export rt_big_div]
def natDiv (a b : Limbs) : Limbs := if b.size == 0 then Array.mkEmpty 0 else (divide a b).1

/-- For `b` other than zero. -/
@[export rt_big_mod]
def natMod (a b : Limbs) : Limbs := (divide a b).2

/-! ## Powers -/

/- By squaring: `power` runs through a, a^2, a^4, ... and `result` gathers the ones the exponent's bits pick
out. Anything to the power 0 is 1, zero included. -/
def powerLoop (power result : Limbs) (exponent : USize) : Nat → Limbs
  | 0 => result
  | fuel + 1 =>
    if exponent == 0 then result else
    let result := if exponent &&& 1 != 0 then trim (mul result power) else result
    let exponent := exponent >>> 1
    if exponent == 0 then result else powerLoop (trim (mul power power)) result exponent fuel

@[export rt_big_power]
def power (a : Limbs) (exponent : USize) : Limbs := powerLoop a (one ()) exponent 64

/-! ## Integers

A sign, 1 for a number below zero, and the limbs of the number without it. A result is the limbs with the
sign as one more element on the end. -/

def signed (negative : Bool) (limbs : Limbs) : Limbs := limbs.push (low (if negative then 1 else 0))

/-- With the same sign the limbs add; with different signs the smaller comes off the larger, whose sign the
result takes. -/
@[export rt_big_int_add]
def intAdd (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) : Limbs :=
  if an == bn then signed (an != 0) (add a b)
  else
    let order := compare a b
    if order == 1 then signed false (Array.mkEmpty 0)
    else if order == 2 then signed (an != 0) (sub a b)
    else signed (bn != 0) (sub b a)

@[export rt_big_int_mul]
def intMul (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) : Limbs := signed (an != bn) (mul a b)

/-- `Int.ediv`: the division whose remainder is never negative, and `n / 0 = 0`. Dividing the limbs gives
|n| = |d| q + r. If n is not negative, or r is zero, the quotient is q with the sign the signs give it.
Otherwise n = -|d| (q + 1) + (|d| - r), and it is q + 1. -/
@[export rt_big_int_ediv]
def intEdiv (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) : Limbs :=
  if b.size == 0 then signed false (Array.mkEmpty 0) else
  let (q, r) := divide a b
  let q := if an != 0 && (trim r).size != 0 then add q (one ()) else q
  signed (an != bn) q

/-- `Int.emod`, for `d` other than zero: r above, or |d| - r where the quotient was q + 1. -/
@[export rt_big_int_emod]
def intEmod (an : UInt8) (a : Limbs) (b : Limbs) : Limbs :=
  let r := trim (divide a b).2
  signed false (if an != 0 && r.size != 0 then sub b r else r)

/-- 0 if the first is less than the second, 1 if they are equal, 2 if it is greater. -/
@[export rt_big_int_compare]
def intCompare (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) : UInt8 :=
  if an != bn then (if an != 0 then 0 else 2)
  else
    let order := compare a b
    if an != 0 then 2 - order else order

end Runtime.Big
