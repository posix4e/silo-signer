import Runtime.Big

/-! # What the runtime's arithmetic computes

`Runtime/Big.lean` works on limbs. This says what number a row of limbs is, and proves that each operation
returns the limbs of the number it should: the sum, the difference, the product, and so on, as Lean's `Nat`
defines them. Nothing here runs; no image imports it. -/

namespace Runtime.Big

local notation "B" => (4294967296 : Nat)

/-- The number a list of limbs is, least significant first. -/
def valueList : List UInt32 → Nat
  | [] => 0
  | x :: xs => x.toNat + B * valueList xs

/-- The number an array of limbs is. -/
def value (a : Limbs) : Nat := valueList a.toList

/-- The number the limbs from `i` up are. -/
def tail (a : Limbs) (i : Nat) : Nat := valueList (a.toList.drop i)

/-- Limb `i` as a number; zero beyond the end. -/
def digit (a : Limbs) (i : Nat) : Nat := (a.getD i 0).toNat

theorem valueList_append (xs ys : List UInt32) :
    valueList (xs ++ ys) = valueList xs + B ^ xs.length * valueList ys := by
  induction xs with
  | nil => simp [valueList]
  | cons x xs ih =>
    simp only [List.cons_append, valueList, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm, Nat.mul_assoc]

theorem value_push (a : Limbs) (x : UInt32) : value (a.push x) = value a + B ^ a.size * x.toNat := by
  simp [value, Array.toList_push, valueList_append, valueList]

theorem tail_zero (a : Limbs) : tail a 0 = value a := by simp [tail, value]

theorem digit_lt (a : Limbs) (i : Nat) : digit a i < B := (a.getD i 0).toNat_lt

theorem tail_step (a : Limbs) (i : Nat) : tail a i = digit a i + B * tail a (i + 1) := by
  by_cases h : i < a.size
  · have : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]; simp
    simp [tail, digit, this, valueList, Array.getD, h]
  · have h1 : a.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : a.toList.drop (i + 1) = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [tail, digit, h1, h2, valueList, Array.getD, h]

theorem tail_of_le (a : Limbs) (i : Nat) (h : a.size ≤ i) : tail a i = 0 := by
  simp [tail, valueList, List.drop_eq_nil_of_le (show a.toList.length ≤ i by simpa using h)]

theorem limb_toNat (a : Limbs) (i : Nat) : (limb a i).toNat = digit a i := by
  simp [limb, digit]

/-! ## Addition -/

theorem addLoop_value (a b : Limbs) (n i : Nat) (carry : UInt64) (r : Limbs)
    (ha : a.size ≤ n) (hb : b.size ≤ n) (hc : carry.toNat ≤ 1) :
    value (addLoop a b n i carry r) = value r + B ^ r.size * (carry.toNat + tail a i + tail b i) := by
  fun_induction addLoop a b n i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have ht : t.toNat = digit a i + digit b i + carry.toNat := by
      simp only [t, UInt64.toNat_add, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, tail_step b i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega), tail_of_le b i (by omega)]
    simp

/-- The limbs `add` returns are those of the sum. -/
theorem add_value (a b : Limbs) : value (add a b) = value a + value b := by
  simp only [add]
  split <;> rw [addLoop_value _ _ _ _ _ _ (by omega) (by omega) (by decide)] <;>
    simp [value, valueList, tail]

/-! ## Subtraction -/

theorem subLoop_value (a b : Limbs) (i : Nat) (borrow : UInt64) (r : Limbs)
    (hb : borrow.toNat ≤ 1) (h : tail b i + borrow.toNat ≤ tail a i) :
    value (subLoop a b i borrow r) = value r + B ^ r.size * (tail a i - tail b i - borrow.toNat) := by
  fun_induction subLoop a b i borrow r with
  | case1 i borrow r hi t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have sa := tail_step a i; have sb := tail_step b i
    have ht : t.toNat = (digit a i + 18446744073709551616 - digit b i - borrow.toNat) % 18446744073709551616 := by
      simp only [t, UInt64.toNat_sub, limb_toNat]; omega
    have hhigh : (t >>> 63).toNat = t.toNat / 9223372036854775808 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega) (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i borrow r hi =>
    have := tail_of_le a i (by omega)
    have : tail a i - tail b i - borrow.toNat = 0 := by omega
    simp [this]

/-- For `a` at least `b`, the limbs `sub` returns are those of the difference. -/
theorem sub_value (a b : Limbs) (h : value b ≤ value a) : value (sub a b) = value a - value b := by
  simp only [sub]
  rw [subLoop_value _ _ _ _ _ (by decide) (by simpa [tail_zero] using h)]
  simp [value, valueList, tail]

/-! ## Zero limbs on top -/

theorem value_pop (a : Limbs) (h : a.size ≠ 0) (top : a.getD (a.size - 1) 0 = 0) : value a.pop = value a := by
  have ne : a.toList ≠ [] := by intro e; apply h; simpa using congrArg List.length e
  have last : a.toList.getLast ne = 0 := by
    rw [List.getLast_eq_getElem]
    have hlt : a.size - 1 < a.size := by omega
    have := top
    simp [Array.getD, hlt] at this
    simpa using this
  have split := List.dropLast_concat_getLast ne
  rw [last] at split
  have := congrArg valueList split
  rw [valueList_append] at this
  simpa [value, Array.toList_pop, valueList] using this

/-- Taking the zero limbs off the top leaves the same number. -/
theorem trim_value (a : Limbs) : value (trim a) = value a := by
  fun_induction trim a with
  | case1 a h => rfl
  | case2 a h top ih => rw [ih, value_pop a h (by simpa using top)]
  | case3 a h top => rfl

/-! ## Writing a limb -/

theorem value_set (r : Limbs) (k : Nat) (v : UInt32) (h : k < r.size) :
    value (r.setIfInBounds k v) + B ^ k * digit r k = value r + B ^ k * v.toNat := by
  have hk : k < r.toList.length := by simpa using h
  have before : r.toList = r.toList.take k ++ r[k] :: r.toList.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k r.toList, List.drop_eq_getElem_cons hk]
    simp
  have after : (r.setIfInBounds k v).toList = r.toList.take k ++ v :: r.toList.drop (k + 1) := by
    simp [Array.toList_setIfInBounds, List.set_eq_take_append_cons_drop]
    intro hle; omega
  have len : (r.toList.take k).length = k := by simp; omega
  have d : digit r k = r[k].toNat := by simp [digit, Array.getD, h]
  rw [value, after, valueList_append, len, d]
  conv => rhs; rw [value, before, valueList_append, len]
  simp only [valueList]
  generalize valueList (r.toList.take k) = low
  generalize valueList (r.toList.drop (k + 1)) = high
  generalize B ^ k = P
  rw [Nat.mul_add, Nat.mul_add]
  omega

theorem digit_set_ne (r : Limbs) (k m : Nat) (v : UInt32) (h : m ≠ k) :
    digit (r.setIfInBounds k v) m = digit r m := by
  simp [digit, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-! ## Multiplication by one limb, and decimal literals -/

theorem scaleLoop_value (a : Limbs) (m : UInt64) (i : Nat) (carry : UInt64) (r : Limbs)
    (hm : m.toNat < B) (hc : carry.toNat < B) :
    value (scaleLoop a m i carry r) = value r + B ^ r.size * (carry.toNat + m.toNat * tail a i) := by
  fun_induction scaleLoop a m i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i
    have bound : digit a i * m.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have ht : t.toNat = digit a i * m.toNat + carry.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_add m.toNat, Nat.mul_left_comm m.toNat,
      Nat.mul_comm m.toNat (digit a i)]
    congr 2
    generalize m.toNat * tail a (i + 1) = rest
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega)]
    simp

/-- One more digit of a decimal literal. -/
theorem decimal_value (a : Limbs) (d : UInt32) : value (decimal a d) = value a * 10 + d.toNat := by
  have hd := d.toNat_lt
  rw [decimal, trim_value, scaleLoop_value _ _ _ _ _ (by decide) (by simpa using hd)]
  simp [value, valueList, tail_zero, Nat.mul_comm, Nat.add_comm]

/-! ## Multiplication -/

theorem mulRow_size (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs) :
    (mulRow a x i j carry r).size = r.size := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih => simp [ih]
  | case2 j carry r h => simp

theorem mulRow_digit (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs) (m : Nat)
    (hm : i + a.size < m) : digit (mulRow a x i j carry r) m = digit r m := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih => rw [ih, digit_set_ne _ _ _ _ (by omega)]
  | case2 j carry r h => rw [digit_set_ne _ _ _ _ (by omega)]

/-- A row of the multiplication adds `x` times what is left of `a`, and the carry, at its place. -/
theorem mulRow_value (a : Limbs) (x : UInt64) (i j : Nat) (carry : UInt64) (r : Limbs)
    (hx : x.toNat < B) (hc : carry.toNat < B) (hj : j ≤ a.size) (hsize : i + a.size < r.size)
    (htop : digit r (i + a.size) = 0) :
    value (mulRow a x i j carry r) = value r + B ^ (i + j) * (carry.toNat + x.toNat * tail a j) := by
  fun_induction mulRow a x i j carry r with
  | case1 j carry r h t ih =>
    have la := digit_lt a j; have ld := digit_lt r (i + j)
    have bound : digit a j * x.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have ht : t.toNat = digit a j * x.toNat + digit r (i + j) + carry.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    have written := value_set r (i + j) t.toUInt32 (by omega)
    rw [ih (by rw [hhigh]; omega) (by omega) (by simpa using hsize) (by rw [digit_set_ne _ _ _ _ (by omega)]; exact htop),
      hhigh, show i + (j + 1) = i + j + 1 from rfl, Nat.pow_succ, tail_step a j, Nat.mul_add x.toNat,
      Nat.mul_left_comm x.toNat, Nat.mul_comm x.toNat (digit a j)]
    rw [hlow] at written
    generalize digit a j * x.toNat = product at *
    generalize x.toNat * tail a (j + 1) = rest at *
    generalize value (r.setIfInBounds (i + j) t.toUInt32) = after at *
    generalize B ^ (i + j) = P at *
    generalize t.toNat = T at *
    have inner : T % B + B * (T / B + rest) = carry.toNat + (product + B * rest) + digit r (i + j) := by omega
    have scaled := congrArg (P * ·) inner
    simp only [Nat.mul_add, Nat.mul_assoc] at scaled written ⊢
    omega
  | case2 j carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    have written := value_set r (i + a.size) carry.toUInt32 hsize
    rw [htop, hlow] at written
    have : j = a.size := by omega
    subst this
    rw [tail_of_le a _ (Nat.le_refl _)]
    simpa using written

theorem valueList_replicate (n : Nat) : valueList (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, valueList, ih]

theorem value_zeros (n : Nat) : value (zeros n) = 0 := by
  simp [value, zeros, low, valueList_replicate]

theorem digit_zeros (n m : Nat) : digit (zeros n) m = 0 := by
  unfold digit zeros low
  by_cases h : m < n <;> simp [Array.getD, h]

theorem mulLoop_value (a b : Limbs) (i : Nat) (r : Limbs)
    (hsize : r.size = a.size + b.size) (hzero : ∀ m, i + a.size ≤ m → digit r m = 0) :
    value (mulLoop a b i r) = value r + B ^ i * (value a * tail b i) := by
  fun_induction mulLoop a b i r with
  | case1 i r h ih =>
    have lb := digit_lt b i
    have row := mulRow_value a (limb b i) i 0 0 r (by rw [limb_toNat]; exact lb) (by decide) (Nat.zero_le _)
      (by omega) (hzero _ (Nat.le_refl _))
    rw [ih (by rw [mulRow_size]; exact hsize)
        (fun m hm => by rw [mulRow_digit _ _ _ _ _ _ _ (by omega)]; exact hzero m (by omega)),
      row, limb_toNat, tail_zero, Nat.pow_succ, tail_step b i, Nat.mul_add (value a), Nat.mul_left_comm (value a)]
    simp only [Nat.add_zero, show (0 : UInt64).toNat = 0 from rfl, Nat.zero_add, Nat.mul_comm (digit b i) (value a)]
    generalize value a * digit b i = product
    generalize value a * tail b (i + 1) = rest
    generalize B ^ i = P
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  | case2 i r h => simp [tail_of_le b i (by omega)]

/-- The limbs `mul` returns are those of the product. -/
theorem mul_value (a b : Limbs) : value (mul a b) = value a * value b := by
  rw [mul, mulLoop_value a b 0 _ (by simp [zeros]) (fun m _ => digit_zeros _ m), value_zeros, tail_zero]
  simp

/-! ## Comparison -/

/-- The number the limbs below `i` are. -/
def lower (a : Limbs) : Nat → Nat
  | 0 => 0
  | i + 1 => lower a i + B ^ i * digit a i

theorem value_split (a : Limbs) (i : Nat) : value a = lower a i + B ^ i * tail a i := by
  induction i with
  | zero => simp [lower, tail_zero]
  | succ i ih =>
    rw [ih, tail_step a i, lower, Nat.pow_succ]
    generalize B ^ i = P
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega

theorem lower_lt (a : Limbs) (i : Nat) : lower a i < B ^ i := by
  induction i with
  | zero => simp [lower]
  | succ i ih =>
    have d := digit_lt a i
    have : B ^ i * digit a i ≤ B ^ i * 4294967295 := Nat.mul_le_mul_left _ (by omega)
    rw [lower, Nat.pow_succ]
    generalize B ^ i = P at *
    omega

/-- 0, 1 or 2 as the first is smaller than, equal to or larger than the second: what `compare` answers. -/
def order (x y : Nat) : UInt8 := if x < y then 0 else if x = y then 1 else 2

theorem compareFrom_order (a b : Limbs) (i : Nat) (same : tail a i = tail b i) :
    compareFrom a b i = order (value a) (value b) := by
  induction i with
  | zero => simp [compareFrom, order, ← tail_zero, same]
  | succ i ih =>
    have sa := value_split a (i + 1); have sb := value_split b (i + 1)
    have la := lower_lt a i; have lb := lower_lt b i
    have da := digit_lt a i; have db := digit_lt b i
    rw [same] at sa
    simp only [lower, Nat.pow_succ] at sa sb
    simp only [compareFrom, UInt64.lt_iff_toNat_lt, limb_toNat]
    by_cases h1 : digit a i < digit b i
    · have : B ^ i * (digit a i + 1) ≤ B ^ i * digit b i := Nat.mul_le_mul_left _ (by omega)
      simp only [h1, ↓reduceIte, order]
      generalize B ^ i = P at *
      generalize P * B * tail b (i + 1) = high at *
      simp only [Nat.mul_add, Nat.mul_one] at this
      have : value a < value b := by omega
      simp [this]
    · by_cases h2 : digit b i < digit a i
      · have : B ^ i * (digit b i + 1) ≤ B ^ i * digit a i := Nat.mul_le_mul_left _ (by omega)
        simp only [h1, h2, ↓reduceIte, order]
        generalize B ^ i = P at *
        generalize P * B * tail b (i + 1) = high at *
        simp only [Nat.mul_add, Nat.mul_one] at this
        have : value b < value a := by omega
        have h3 : ¬ value a < value b := by omega
        have h4 : value a ≠ value b := by omega
        simp [h3, h4]
      · have eq : digit a i = digit b i := by omega
        simp only [h1, h2, ↓reduceIte]
        exact ih (by rw [tail_step a i, tail_step b i, eq, same])

/-- No zero limb on top: how a number arrives, and what `trim` leaves. -/
def Trimmed (a : Limbs) : Prop := a.size = 0 ∨ digit a (a.size - 1) ≠ 0

theorem value_lt_pow (a : Limbs) : value a < B ^ a.size := by
  have := value_split a a.size
  rw [tail_of_le a _ (Nat.le_refl _)] at this
  have := lower_lt a a.size
  omega

theorem pow_le_value (a : Limbs) (h : a.size ≠ 0) (t : Trimmed a) : B ^ (a.size - 1) ≤ value a := by
  have top : digit a (a.size - 1) ≠ 0 := by rcases t with z | nz; exact absurd z h; exact nz
  have s := value_split a (a.size - 1)
  rw [tail_step a (a.size - 1)] at s
  have : B ^ (a.size - 1) * 1 ≤ B ^ (a.size - 1) * (digit a (a.size - 1) + B * tail a (a.size - 1 + 1)) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem value_lt_of_shorter (a b : Limbs) (h : a.size < b.size) (t : Trimmed b) : value a < value b := by
  have ha := value_lt_pow a
  have hb := pow_le_value b (by omega) t
  have : B ^ a.size ≤ B ^ (b.size - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

/-- On numbers with no zero limb on top, `compare` says which is larger. -/
theorem compare_order (a b : Limbs) (ta : Trimmed a) (tb : Trimmed b) : compare a b = order (value a) (value b) := by
  simp only [compare]
  by_cases h1 : a.size < b.size
  · simp [h1, order, value_lt_of_shorter a b h1 tb]
  · by_cases h2 : b.size < a.size
    · have := value_lt_of_shorter b a h2 ta
      have h3 : ¬ value a < value b := by omega
      have h4 : value a ≠ value b := by omega
      simp [h1, h2, order, h3, h4]
    · simp only [h1, h2, ↓reduceIte]
      exact compareFrom_order a b a.size (by rw [tail_of_le a _ (Nat.le_refl _), tail_of_le b _ (by omega)])

/-- Subtraction of natural numbers: the difference, or zero where there is none. -/
theorem natSub_value (a b : Limbs) (ta : Trimmed a) (tb : Trimmed b) : value (natSub a b) = value a - value b := by
  simp only [natSub, compare_order a b ta tb, order]
  by_cases h1 : value a < value b
  · have z : value a - value b = 0 := by omega
    simp only [h1, ↓reduceIte, show ((0 : UInt8) == 2) = false from rfl, Bool.false_eq_true, z]
    rfl
  · by_cases h2 : value a = value b
    · simp only [h2, Nat.lt_irrefl, ↓reduceIte, show ((1 : UInt8) == 2) = false from rfl, Bool.false_eq_true,
        Nat.sub_self]
      rfl
    · simp only [h1, h2, ↓reduceIte, show ((2 : UInt8) == 2) = true from rfl]
      exact sub_value a b (by omega)

/-! ## And, or -/

/-- What `bitsLoop` does to a pair of limbs, done to a pair of numbers. -/
def bitOp (either : Bool) (x y : Nat) : Nat := if either then x ||| y else x &&& y

/-- The bits of a number are the bits of its lowest limb and the bits of the rest. -/
theorem bitOp_split (either : Bool) (x y p q : Nat) (hx : x < B) (hy : y < B) :
    bitOp either (x + B * p) (y + B * q) = bitOp either x y + B * bitOp either p q := by
  have ex : x + B * p = 2 ^ 32 * p + x := by omega
  have ey : y + B * q = 2 ^ 32 * q + y := by omega
  have hx' : x < 2 ^ 32 := by omega
  have hy' : y < 2 ^ 32 := by omega
  cases either
  · have hr : x &&& y < 2 ^ 32 := Nat.and_lt_two_pow x hy'
    have er : (x &&& y) + B * (p &&& q) = 2 ^ 32 * (p &&& q) + (x &&& y) := by omega
    simp only [bitOp, Bool.false_eq_true, ↓reduceIte]
    rw [ex, ey, er]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hx', Nat.testBit_two_pow_mul_add _ hy',
      Nat.testBit_two_pow_mul_add _ hr]
    split <;> simp [Nat.testBit_and]
  · have hr : x ||| y < 2 ^ 32 := Nat.or_lt_two_pow hx' hy'
    have er : (x ||| y) + B * (p ||| q) = 2 ^ 32 * (p ||| q) + (x ||| y) := by omega
    simp only [bitOp, ↓reduceIte]
    rw [ex, ey, er]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add _ hx', Nat.testBit_two_pow_mul_add _ hy',
      Nat.testBit_two_pow_mul_add _ hr]
    split <;> simp [Nat.testBit_or]

theorem bitsLoop_value (a b : Limbs) (either : Bool) (n i : Nat) (r : Limbs)
    (hend : ∀ k, n ≤ k → bitOp either (tail a k) (tail b k) = 0) :
    value (bitsLoop a b either n i r) = value r + B ^ r.size * bitOp either (tail a i) (tail b i) := by
  fun_induction bitsLoop a b either n i r with
  | case1 i r h x ih =>
    have hx : x.toNat = bitOp either (digit a i) (digit b i) := by
      cases either <;> simp [x, bitOp, digit]
    rw [ih, value_push, Array.size_push, Nat.pow_succ, hx, tail_step a i, tail_step b i,
      bitOp_split _ _ _ _ _ (digit_lt a i) (digit_lt b i), Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
  | case2 i r h => simp [hend i (by omega)]

/-- The limbs `and` returns are those of the number with the bits both have. -/
theorem and_value (a b : Limbs) : value (Runtime.Big.and a b) = value a &&& value b := by
  have hend : ∀ k, (if a.size < b.size then a.size else b.size) ≤ k → bitOp false (tail a k) (tail b k) = 0 := by
    intro k hk
    by_cases h : a.size ≤ k
    · simp [bitOp, tail_of_le a k h]
    · have : b.size ≤ k := by split at hk <;> omega
      simp [bitOp, tail_of_le b k this]
  simp only [Runtime.Big.and]
  rw [bitsLoop_value _ _ _ _ _ _ hend]
  simp [bitOp, value, valueList, tail]

/-- The limbs `or` returns are those of the number with the bits either has. -/
theorem or_value (a b : Limbs) : value (Runtime.Big.or a b) = value a ||| value b := by
  have hend : ∀ k, (if a.size < b.size then b.size else a.size) ≤ k → bitOp true (tail a k) (tail b k) = 0 := by
    intro k hk
    have ha : a.size ≤ k := by split at hk <;> omega
    have hb : b.size ≤ k := by split at hk <;> omega
    simp [bitOp, tail_of_le a k ha, tail_of_le b k hb]
  simp only [Runtime.Big.or]
  rw [bitsLoop_value _ _ _ _ _ _ hend]
  simp [bitOp, value, valueList, tail]

/-! ## Shifts -/

theorem tail_eq_div (a : Limbs) (i : Nat) : tail a i = value a / B ^ i := by
  rw [value_split a i, Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide)), Nat.div_eq_of_lt (lower_lt a i),
    Nat.zero_add]

theorem shiftLeftLoop_value (a : Limbs) (bits : UInt64) (i : Nat) (carry : UInt64) (r : Limbs)
    (hb : bits.toNat < 32) (hc : carry.toNat < 2 ^ bits.toNat) :
    value (shiftLeftLoop a bits i carry r) = value r + B ^ r.size * (carry.toNat + 2 ^ bits.toNat * tail a i) := by
  have hp : 2 ^ bits.toNat ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) (by omega)
  fun_induction shiftLeftLoop a bits i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i
    have scaled : digit a i * 2 ^ bits.toNat ≤ 4294967295 * 2 ^ bits.toNat := Nat.mul_le_mul_right _ (by omega)
    have ht : t.toNat = digit a i * 2 ^ bits.toNat + carry.toNat := by
      have e1 : bits.toNat % 64 = bits.toNat := Nat.mod_eq_of_lt (by omega)
      have e2 : digit a i <<< bits.toNat = digit a i * 2 ^ bits.toNat := Nat.shiftLeft_eq _ _
      simp only [t, UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat, e1]
      rw [Nat.mod_eq_of_lt (by rw [e2]; generalize 2 ^ bits.toNat = P at *; omega),
        ← Nat.shiftLeft_add_eq_or_of_lt hc, e2]
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; generalize 2 ^ bits.toNat = P at *; omega), value_push, Array.size_push, Nat.pow_succ,
      hhigh, hlow, tail_step a i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_add (2 ^ bits.toNat),
      Nat.mul_left_comm (2 ^ bits.toNat), Nat.mul_comm (2 ^ bits.toNat) (digit a i)]
    congr 2
    generalize 2 ^ bits.toNat * tail a (i + 1) = rest
    generalize 2 ^ bits.toNat = P at *
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega)]
    simp

/-- `shiftLeft` multiplies by two for every bit and 2^32 for every whole limb. -/
theorem shiftLeft_value (a : Limbs) (whole : Nat) (bits : UInt64) (hb : bits.toNat < 32) :
    value (shiftLeft a whole bits) = value a * 2 ^ (32 * whole + bits.toNat) := by
  have hB : B ^ whole = 2 ^ (32 * whole) := by rw [Nat.pow_mul]
  rw [shiftLeft, shiftLeftLoop_value _ _ _ _ _ hb (Nat.two_pow_pos _), value_zeros, tail_zero, Nat.pow_add, ← hB]
  simp [zeros, Nat.mul_comm, Nat.mul_assoc]

/-- A shift left by any number of bits a machine word can count multiplies by two that many times. -/
theorem shiftLeftBy_value (a : Limbs) (shift : USize) :
    value (shiftLeftBy a shift) = value a * 2 ^ shift.toNat := by
  have h32 : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
  have whole : (shift / 32).toNat = shift.toNat / 32 := by rw [USize.toNat_div, h32]
  have bits : (shift % 32).toUInt64.toNat = shift.toNat % 32 := by rw [USize.toNat_toUInt64, USize.toNat_mod, h32]
  rw [shiftLeftBy, shiftLeft_value _ _ _ (by rw [bits]; omega), whole, bits]
  congr 2
  omega

/-- Dividing two limbs and all above them by a power of two that divides the base: the lowest limb of the
answer comes from the lowest two, and the rest is the same division one limb up. -/
theorem shift_split (K M N d0 d1 T : Nat) (hK : 0 < K) (hN : K * M = N) (h0 : d0 < N) :
    (d0 + N * (d1 + N * T)) / K = (d0 + N * d1) / K % N + N * ((d1 + N * T) / K) := by
  subst hN
  have e1 : d0 + K * M * (d1 + K * M * T) = (d0 + K * M * d1) + K * (M * (K * M) * T) := by
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have e2 : d1 + K * M * T = d1 + K * (M * T) := by rw [Nat.mul_assoc]
  have e3 : (d0 + K * M * d1) / K / (K * M) = d1 / K := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm K (K * M), ← Nat.div_div_eq_div_mul,
      Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h0, Nat.zero_add]
  have e4 := Nat.mod_add_div ((d0 + K * M * d1) / K) (K * M)
  rw [e3] at e4
  rw [e1, Nat.add_mul_div_left _ _ hK, e2, Nat.add_mul_div_left _ _ hK, Nat.mul_add, ← Nat.add_assoc, e4]
  congr 1
  rw [Nat.mul_comm M (K * M), Nat.mul_assoc]

theorem shiftRightLoop_value (a : Limbs) (bits : UInt64) (n i : Nat) (r : Limbs)
    (hb : bits.toNat < 32) (hn : value a < B ^ n) :
    value (shiftRightLoop a bits n i r) = value r + B ^ r.size * (tail a i / 2 ^ bits.toNat) := by
  fun_induction shiftRightLoop a bits n i r with
  | case1 i r h t ih =>
    have l0 := digit_lt a i; have l1 := digit_lt a (i + 1)
    have ht : t.toNat = (digit a i + B * digit a (i + 1)) / 2 ^ bits.toNat := by
      have e1 : bits.toNat % 64 = bits.toNat := Nat.mod_eq_of_lt (by omega)
      have e2 : digit a (i + 1) <<< 32 % 2 ^ 64 = digit a (i + 1) <<< 32 :=
        Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
      simp only [t, UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat, e1]
      rw [show (32 : UInt64).toNat % 64 = 32 from rfl, e2,
        ← Nat.shiftLeft_add_eq_or_of_lt (show digit a i < 2 ^ 32 by omega), Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow,
        show digit a (i + 1) * 2 ^ 32 + digit a i = digit a i + B * digit a (i + 1) by omega]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    have hKM : 2 ^ bits.toNat * 2 ^ (32 - bits.toNat) = B := by
      rw [← Nat.pow_add, show bits.toNat + (32 - bits.toNat) = 32 by omega]
    have key : tail a i / 2 ^ bits.toNat = t.toNat % B + B * (tail a (i + 1) / 2 ^ bits.toNat) := by
      rw [ht, tail_step a i, tail_step a (i + 1)]
      exact shift_split _ _ _ _ _ _ (Nat.two_pow_pos _) hKM l0
    rw [ih, value_push, Array.size_push, Nat.pow_succ, hlow, key, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
  | case2 i r h =>
    have z : tail a i = 0 := by
      rw [tail_eq_div]
      exact Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hn (Nat.pow_le_pow_right (by omega) (by omega)))
    simp [z]

/-- `shiftRight` over limbs that hold the whole of a number divides by two for every bit and 2^32 for every
whole limb, rounding down. -/
theorem shiftRight_value (a : Limbs) (whole n : Nat) (bits : UInt64) (hb : bits.toNat < 32)
    (hn : value a < B ^ n) :
    value (shiftRight a whole n bits) = value a / 2 ^ (32 * whole + bits.toNat) := by
  have hB : B ^ whole = 2 ^ (32 * whole) := by rw [Nat.pow_mul]
  rw [shiftRight, shiftRightLoop_value _ _ _ _ _ hb hn, tail_eq_div, Nat.div_div_eq_div_mul, Nat.pow_add, ← hB]
  simp [value, valueList]

/-- A shift right by any number of bits a machine word can count halves that many times, rounding down. -/
theorem shiftRightBy_value (a : Limbs) (shift : USize) :
    value (shiftRightBy a shift) = value a / 2 ^ shift.toNat := by
  have h32 : (32 : USize).toNat = 32 := USize.toNat_ofNat_of_lt_32 (by decide)
  have whole : (shift / 32).toNat = shift.toNat / 32 := by rw [USize.toNat_div, h32]
  have bits : (shift % 32).toUInt64.toNat = shift.toNat % 32 := by rw [USize.toNat_toUInt64, USize.toNat_mod, h32]
  rw [shiftRightBy, shiftRight_value _ _ _ _ (by rw [bits]; omega) (value_lt_pow a), whole, bits]
  congr 2
  omega

/-! ## Division, where the divisor is one limb or the dividend is shorter

Long division by two limbs or more (`divideLong`) comes after these. -/

theorem lower_size (a : Limbs) : lower a a.size = value a := by
  have := value_split a a.size
  rw [tail_of_le a _ (Nat.le_refl _)] at this
  simpa using this.symm

/-- Division by one limb, from limb `i` down, with `rest` carried in from above: what it adds to the
quotient, times the divisor, and what it leaves, make up `rest` and the limbs below `i`. -/
theorem divideSmallLoop_value (a : Limbs) (d rest : UInt64) (q : Limbs) (i : Nat)
    (hd : d.toNat < B) (hr : rest.toNat < d.toNat) (hi : i ≤ q.size) (hz : ∀ m, m < i → digit q m = 0) :
    value (divideSmallLoop a d rest q i).1 * d.toNat + value (divideSmallLoop a d rest q i).2
        = value q * d.toNat + rest.toNat * B ^ i + lower a i
      ∧ value (divideSmallLoop a d rest q i).2 < d.toNat := by
  induction i generalizing rest q with
  | zero =>
    have low : rest.toUInt32.toNat = rest.toNat := by simp only [UInt64.toNat_toUInt32]; omega
    simp only [divideSmallLoop, value_push, lower, low]
    simp [value, valueList]
    exact hr
  | succ i ih =>
    have la := digit_lt a i
    have dpos : 0 < d.toNat := by omega
    simp only [divideSmallLoop]
    generalize hp : (rest <<< 32) ||| limb a i = part
    have hpart : part.toNat = rest.toNat * B + digit a i := by
      subst hp
      have e : rest.toNat <<< 32 % 2 ^ 64 = rest.toNat <<< 32 :=
        Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
      simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, limb_toNat]
      rw [show (32 : UInt64).toNat % 64 = 32 from rfl, e,
        ← Nat.shiftLeft_add_eq_or_of_lt (show digit a i < 2 ^ 32 by omega), Nat.shiftLeft_eq]
    have hq : (part / d).toNat = part.toNat / d.toNat := UInt64.toNat_div _ _
    have hm : (part % d).toNat = part.toNat % d.toNat := UInt64.toNat_mod _ _
    have qlt : part.toNat / d.toNat < B := by
      rw [Nat.div_lt_iff_lt_mul dpos]
      have : (rest.toNat + 1) * B ≤ d.toNat * B := Nat.mul_le_mul_right _ (by omega)
      omega
    have hlow : (part / d).toUInt32.toNat = part.toNat / d.toNat := by
      simp only [UInt64.toNat_toUInt32, hq]; omega
    have step := ih (part % d) (q.setIfInBounds i (part / d).toUInt32) (by rw [hm]; exact Nat.mod_lt _ dpos)
      (by simp; omega) (fun m hm' => by rw [digit_set_ne _ _ _ _ (by omega)]; exact hz m (by omega))
    have written := value_set q i (part / d).toUInt32 (by omega)
    rw [hz i (by omega), hlow] at written
    have e : value (q.setIfInBounds i (part / d).toUInt32) = value q + B ^ i * (part.toNat / d.toNat) := by
      simpa using written
    have dm := Nat.div_add_mod part.toNat d.toNat
    have key : B ^ i * (part.toNat / d.toNat) * d.toNat + part.toNat % d.toNat * B ^ i
        = rest.toNat * (B ^ i * B) + B ^ i * digit a i := by
      calc B ^ i * (part.toNat / d.toNat) * d.toNat + part.toNat % d.toNat * B ^ i
          = B ^ i * (d.toNat * (part.toNat / d.toNat) + part.toNat % d.toNat) := by
            rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_comm (part.toNat / d.toNat),
              Nat.mul_comm (part.toNat % d.toNat)]
        _ = B ^ i * (rest.toNat * B + digit a i) := by rw [dm, hpart]
        _ = rest.toNat * (B ^ i * B) + B ^ i * digit a i := by rw [Nat.mul_add, Nat.mul_left_comm]
    refine ⟨?_, step.2⟩
    rw [step.1, e, hm, lower, Nat.pow_succ, Nat.add_mul]
    omega

/-- Division by a single limb that is not zero gives the quotient and the remainder. -/
theorem divideSmall_value (a : Limbs) (d : UInt64) (hd : d.toNat < B) (hz : d.toNat ≠ 0) :
    value (divideSmallLoop a d 0 (zeros a.size) a.size).1 = value a / d.toNat ∧
    value (divideSmallLoop a d 0 (zeros a.size) a.size).2 = value a % d.toNat := by
  have zero : (0 : UInt64).toNat = 0 := rfl
  have h := divideSmallLoop_value a d 0 (zeros a.size) a.size hd (by omega) (by simp [zeros])
    (fun m _ => digit_zeros _ m)
  rw [value_zeros, zero, lower_size] at h
  have whole : value (divideSmallLoop a d 0 (zeros a.size) a.size).2 +
      d.toNat * value (divideSmallLoop a d 0 (zeros a.size) a.size).1 = value a := by
    rw [Nat.add_comm, Nat.mul_comm]; simpa using h.1
  have both := (Nat.div_mod_unique (by omega : 0 < d.toNat)).mpr ⟨whole, h.2⟩
  exact ⟨both.1.symm, both.2.symm⟩

theorem value_single (b : Limbs) (h : b.size = 1) : value b = digit b 0 := by
  have s := value_split b 1
  rw [tail_of_le b 1 (by omega)] at s
  simpa [lower] using s

/-- `divide`, for a divisor of one limb that is not zero: the quotient rounded down and the remainder. -/
theorem divide_value_single (a b : Limbs) (h : b.size = 1) (hz : value b ≠ 0) :
    value (divide a b).1 = value a / value b ∧ value (divide a b).2 = value a % value b := by
  have vb := value_single b h
  have lb := digit_lt b 0
  unfold divide
  by_cases short : a.size < b.size
  · have empty : value a = 0 := by
      have := value_lt_pow a
      rw [show a.size = 0 by omega] at this
      simpa using this
    simp only [short, ↓reduceIte]
    rw [empty, Nat.zero_div, Nat.zero_mod]
    exact ⟨rfl, rfl⟩
  · simp only [short, ↓reduceIte]
    simp only [h, beq_self_eq_true, ↓reduceIte]
    rw [vb, ← limb_toNat]
    exact divideSmall_value a (limb b 0) (by rw [limb_toNat]; exact lb) (by rw [limb_toNat]; omega)

/-- `divide`, for a dividend with fewer limbs than the divisor: nothing, and the dividend left over. -/
theorem divide_value_shorter (a b : Limbs) (h : a.size < b.size) (tb : Trimmed b) :
    value (divide a b).1 = value a / value b ∧ value (divide a b).2 = value a % value b := by
  have lt := value_lt_of_shorter a b h tb
  simp only [divide, h, ↓reduceIte]
  rw [Nat.div_eq_of_lt lt, Nat.mod_eq_of_lt lt]
  exact ⟨rfl, rfl⟩

/-! ## Long division

Knuth's algorithm D (The Art of Computer Programming, volume 2, section 4.3.1), a step at a time: taking a
multiple of the divisor off (D4), putting the divisor back once (D6), the guess at a quotient limb (D3), and
then the loop over the quotient's limbs. -/

theorem tail_of_value_lt (a : Limbs) (k : Nat) (h : value a < B ^ k) : tail a k = 0 := by
  rw [tail_eq_div, Nat.div_eq_of_lt h]

theorem value_lt_of_tail (a : Limbs) (k : Nat) (h : tail a k = 0) : value a < B ^ k := by
  have s := value_split a k
  have l := lower_lt a k
  rw [h] at s
  omega

/-- Writing a limb leaves the limbs above it as they were. -/
theorem tail_set_above (r : Limbs) (k m : Nat) (x : UInt32) (h : k < m) :
    tail (r.setIfInBounds k x) m = tail r m := by
  simp [tail, Array.toList_setIfInBounds, List.drop_set_of_lt h]

/-! ### D4: taking a multiple of the divisor off -/

theorem takeLoop_size (v : Limbs) (g : UInt64) (j i : Nat) (carry borrow : UInt64) (u : Limbs) :
    (takeLoop v g j i carry borrow u).1.size = u.size := by
  fun_induction takeLoop v g j i carry borrow u with
  | case1 i carry borrow u h product difference ih => simp [ih]
  | case2 i carry borrow u h difference => simp

theorem takeLoop_tail (v : Limbs) (g : UInt64) (j i : Nat) (carry borrow : UInt64) (u : Limbs) (m : Nat)
    (hm : j + v.size < m) : tail (takeLoop v g j i carry borrow u).1 m = tail u m := by
  fun_induction takeLoop v g j i carry borrow u with
  | case1 i carry borrow u h product difference ih => rw [ih, tail_set_above _ _ _ _ (by omega)]
  | case2 i carry borrow u h difference => exact tail_set_above _ _ _ _ (by omega)

/-- `takeLoop` takes `g` times what is left of `v`, with the carry and the borrow, off `u` at its place. If
that goes below zero it says so, and what it leaves is too large by one in the limb above the last it
wrote. -/
theorem takeLoop_value (v : Limbs) (g : UInt64) (j i : Nat) (carry borrow : UInt64) (u : Limbs)
    (hg : g.toNat < B) (hc : carry.toNat < B) (hb : borrow.toNat ≤ 1) (hi : i ≤ v.size)
    (hu : j + v.size < u.size) :
    value (takeLoop v g j i carry borrow u).1
          + B ^ (i + j) * (carry.toNat + borrow.toNat + g.toNat * tail v i)
        = value u + B ^ (j + v.size + 1) * (takeLoop v g j i carry borrow u).2.toNat
      ∧ (takeLoop v g j i carry borrow u).2.toNat ≤ 1 := by
  fun_induction takeLoop v g j i carry borrow u with
  | case1 i carry borrow u h product difference ih =>
    have lv := digit_lt v i; have lu := digit_lt u (i + j)
    have bound : g.toNat * digit v i ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have hproduct : product.toNat = g.toNat * digit v i + carry.toNat := by
      simp only [product, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have mask : (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 := rfl
    have hplow : (product &&& 0xFFFFFFFF).toNat = product.toNat % B := by
      rw [UInt64.toNat_and, mask, Nat.and_two_pow_sub_one_eq_mod]
    have hdiff : difference.toNat =
        (digit u (i + j) + 18446744073709551616 - product.toNat % B - borrow.toNat) % 18446744073709551616 := by
      simp only [difference, UInt64.toNat_sub, limb_toNat, hplow]; omega
    have hhigh : (difference >>> 63).toNat = difference.toNat / 9223372036854775808 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : difference.toUInt32.toNat = difference.toNat % B := by simp
    have hcarry : (product >>> 32).toNat = product.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have written := value_set u (i + j) difference.toUInt32 (by omega)
    have step := ih (by rw [hcarry]; omega) (by rw [hhigh]; omega) (by omega) (by simpa using hu)
    refine ⟨?_, step.2⟩
    have e := step.1
    rw [hcarry, hhigh, show i + 1 + j = i + j + 1 by omega,
      show B ^ (i + j + 1) = B ^ (i + j) * B from Nat.pow_succ ..] at e
    rw [hlow] at written
    rw [tail_step v i, Nat.mul_add g.toNat, Nat.mul_left_comm g.toNat]
    have inner : carry.toNat + borrow.toNat + (g.toNat * digit v i + B * (g.toNat * tail v (i + 1)))
          + difference.toNat % B
        = digit u (i + j)
          + B * (product.toNat / B + difference.toNat / 9223372036854775808 + g.toNat * tail v (i + 1)) := by
      generalize g.toNat * tail v (i + 1) = X
      omega
    have scaled := congrArg (B ^ (i + j) * ·) inner
    generalize value (takeLoop v g j (i + 1) (product >>> 32) (difference >>> 63)
      (u.setIfInBounds (i + j) difference.toUInt32)).1 = after at *
    generalize B ^ (j + v.size + 1) * (takeLoop v g j (i + 1) (product >>> 32) (difference >>> 63)
      (u.setIfInBounds (i + j) difference.toUInt32)).2.toNat = over at *
    generalize value (u.setIfInBounds (i + j) difference.toUInt32) = between at *
    generalize g.toNat * tail v (i + 1) = X at *
    generalize g.toNat * digit v i = gd at *
    generalize B ^ (i + j) = P at *
    simp only [Nat.mul_add, Nat.mul_assoc] at scaled written e ⊢
    omega
  | case2 i carry borrow u h difference =>
    have lu := digit_lt u (j + v.size)
    have hdiff : difference.toNat =
        (digit u (j + v.size) + 18446744073709551616 - carry.toNat - borrow.toNat) % 18446744073709551616 := by
      simp only [difference, UInt64.toNat_sub, limb_toNat]; omega
    have hhigh : (difference >>> 63).toNat = difference.toNat / 9223372036854775808 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : difference.toUInt32.toNat = difference.toNat % B := by simp
    have written := value_set u (j + v.size) difference.toUInt32 hu
    have hiv : i = v.size := by omega
    subst hiv
    rw [hlow] at written
    dsimp only
    rw [tail_of_le v _ (Nat.le_refl _), hhigh, Nat.add_comm v.size j, Nat.pow_succ]
    refine ⟨?_, by omega⟩
    have inner : difference.toNat % B + carry.toNat + borrow.toNat
        = digit u (j + v.size) + B * (difference.toNat / 9223372036854775808) := by omega
    have scaled := congrArg (B ^ (j + v.size) * ·) inner
    generalize value (u.setIfInBounds (j + v.size) difference.toUInt32) = after at *
    generalize B ^ (j + v.size) = P at *
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.mul_zero, Nat.add_zero] at scaled written ⊢
    omega

/-! ### D6: putting the divisor back -/

theorem putBackLoop_size (v : Limbs) (j i : Nat) (carry : UInt64) (u : Limbs) :
    (putBackLoop v j i carry u).size = u.size := by
  fun_induction putBackLoop v j i carry u with
  | case1 i carry u h sum ih => simp [ih]
  | case2 i carry u h => simp

theorem putBackLoop_tail (v : Limbs) (j i : Nat) (carry : UInt64) (u : Limbs) (m : Nat)
    (hm : j + v.size < m) : tail (putBackLoop v j i carry u) m = tail u m := by
  fun_induction putBackLoop v j i carry u with
  | case1 i carry u h sum ih => rw [ih, tail_set_above _ _ _ _ (by omega)]
  | case2 i carry u h => exact tail_set_above _ _ _ _ (by omega)

/-- `putBackLoop` adds what is left of `v`, and the carry, to `u` at its place, and drops whatever is carried
out of the limb above the last of `v`: `c`, which is 0 or 1. -/
theorem putBackLoop_value (v : Limbs) (j i : Nat) (carry : UInt64) (u : Limbs)
    (hc : carry.toNat ≤ 1) (hi : i ≤ v.size) (hu : j + v.size < u.size) :
    ∃ c, c ≤ 1 ∧ value (putBackLoop v j i carry u) + B ^ (j + v.size + 1) * c
      = value u + B ^ (i + j) * (carry.toNat + tail v i) := by
  fun_induction putBackLoop v j i carry u with
  | case1 i carry u h sum ih =>
    have lv := digit_lt v i; have lu := digit_lt u (i + j)
    have hsum : sum.toNat = digit u (i + j) + digit v i + carry.toNat := by
      simp only [sum, UInt64.toNat_add, limb_toNat]; omega
    have hhigh : (sum >>> 32).toNat = sum.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : sum.toUInt32.toNat = sum.toNat % B := by simp
    have written := value_set u (i + j) sum.toUInt32 (by omega)
    obtain ⟨c, hc', e⟩ := ih (by rw [hhigh]; omega) (by omega) (by simpa using hu)
    refine ⟨c, hc', ?_⟩
    rw [hhigh, show i + 1 + j = i + j + 1 by omega,
      show B ^ (i + j + 1) = B ^ (i + j) * B from Nat.pow_succ ..] at e
    rw [hlow] at written
    rw [tail_step v i]
    have inner : sum.toNat % B + B * (sum.toNat / B) = digit u (i + j) + digit v i + carry.toNat := by omega
    have scaled := congrArg (B ^ (i + j) * ·) inner
    generalize value (putBackLoop v j (i + 1) (sum >>> 32) (u.setIfInBounds (i + j) sum.toUInt32)) = after at *
    generalize B ^ (j + v.size + 1) * c = over at *
    generalize value (u.setIfInBounds (i + j) sum.toUInt32) = between at *
    generalize B ^ (i + j) = P at *
    simp only [Nat.mul_add, Nat.mul_assoc] at scaled written e ⊢
    omega
  | case2 i carry u h =>
    have lu := digit_lt u (j + v.size)
    have hiv : i = v.size := by omega
    subst hiv
    have hlow : (limb u (j + v.size) + carry).toUInt32.toNat = (digit u (j + v.size) + carry.toNat) % B := by
      simp only [UInt64.toNat_toUInt32, UInt64.toNat_add, limb_toNat]; omega
    have written := value_set u (j + v.size) (limb u (j + v.size) + carry).toUInt32 hu
    rw [hlow] at written
    refine ⟨(digit u (j + v.size) + carry.toNat) / B, by omega, ?_⟩
    rw [tail_of_le v _ (Nat.le_refl _), Nat.add_comm v.size j, Nat.pow_succ]
    have inner : (digit u (j + v.size) + carry.toNat) % B + B * ((digit u (j + v.size) + carry.toNat) / B)
        = digit u (j + v.size) + carry.toNat := by omega
    have scaled := congrArg (B ^ (j + v.size) * ·) inner
    generalize value (u.setIfInBounds (j + v.size) (limb u (j + v.size) + carry).toUInt32) = after at *
    generalize B ^ (j + v.size) = P at *
    simp only [Nat.mul_add, Nat.mul_assoc, Nat.add_zero] at scaled written ⊢
    omega

/-- Two limbs in a word: the first moved up 32 bits, over the second. -/
theorem two_limbs_word (hi lo : UInt64) (hhi : hi.toNat < B) (hlo : lo.toNat < B) :
    ((hi <<< 32) ||| lo).toNat = hi.toNat * B + lo.toNat := by
  have e : hi.toNat <<< 32 % 2 ^ 64 = hi.toNat <<< 32 := Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
  rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, e,
    ← Nat.shiftLeft_add_eq_or_of_lt (show lo.toNat < 2 ^ 32 by omega), Nat.shiftLeft_eq]

theorem toNat_pred (g : UInt64) (h : 0 < g.toNat) : (g - 1).toNat = g.toNat - 1 := by
  have := g.toNat_lt
  rw [UInt64.toNat_sub, show (1 : UInt64).toNat = 1 from rfl]; omega

/-! ### D3: the guess at a quotient limb

`V` is the divisor and `U` what it is being divided into at this step, each cut below its top limbs:
`V = (v1 B + v2) P + Vl` and `U = (top B + u2) P + Ul`, where `top` is the top two limbs of `U`. -/

/-- If `q` times a number is no more than another, the same holds of their tops. -/
theorem mul_top_le (q x y z w M : Nat) (hw : w < M) (h : q * (x * M + y) ≤ z * M + w) : q * x ≤ z := by
  have h1 : q * x * M ≤ q * (x * M + y) := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  have h2 : q * x * M < (z + 1) * M := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h2)

/-- A guess that fails the test on the second limb is too large. -/
theorem guess_too_large (g v1 v2 rhat top u2 P Vl Ul : Nat)
    (hinv : g * v1 + rhat = top) (htest : rhat * B + u2 < g * v2) (hUl : Ul < P) :
    (top * B + u2) * P + Ul < g * ((v1 * B + v2) * P + Vl) := by
  have h1 : top * B + u2 + 1 ≤ g * (v1 * B + v2) := by
    rw [← hinv, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; omega
  have h2 : (top * B + u2 + 1) * P ≤ g * (v1 * B + v2) * P := Nat.mul_le_mul_right _ h1
  have h3 : g * ((v1 * B + v2) * P + Vl) = g * (v1 * B + v2) * P + g * Vl := by
    rw [Nat.mul_add, Nat.mul_assoc]
  have h4 : (top * B + u2 + 1) * P = (top * B + u2) * P + P := by rw [Nat.add_mul, Nat.one_mul]
  rw [h4] at h2
  rw [h3]
  omega

/-- A guess that passes the test on the second limb is at most one too large. -/
theorem guess_close (g v1 v2 rhat top u2 P Vl Ul : Nat)
    (hinv : g * v1 + rhat = top) (htest : g * v2 ≤ rhat * B + u2) (hg : g < B) (hv1 : 0 < v1) (hVl : Vl < P) :
    g * ((v1 * B + v2) * P + Vl) < ((top * B + u2) * P + Ul) + ((v1 * B + v2) * P + Vl) := by
  have h1 : g * (v1 * B + v2) ≤ top * B + u2 := by
    rw [← hinv, Nat.mul_add, Nat.add_mul, Nat.mul_assoc]; omega
  have h2 : g * (v1 * B + v2) * P ≤ (top * B + u2) * P := Nat.mul_le_mul_right _ h1
  have h3 : g * ((v1 * B + v2) * P + Vl) = g * (v1 * B + v2) * P + g * Vl := by
    rw [Nat.mul_add, Nat.mul_assoc]
  have h4 : g * Vl ≤ g * P := Nat.mul_le_mul_left _ (by omega)
  have h5 : (g + 1) * P ≤ B * P := Nat.mul_le_mul_right _ (by omega)
  have h6 : B * P ≤ (v1 * B + v2) * P := Nat.mul_le_mul_right _ (by omega)
  rw [Nat.add_mul, Nat.one_mul] at h5
  rw [h3]
  omega

/-- What a guess at a quotient limb has to be for the step to come out: a limb, never too small, and at
most one too large. -/
def GoodGuess (r U V : Nat) : Prop := r < B ∧ (∀ q, q * V ≤ U → q ≤ r) ∧ r * V < U + V

/-- `refine` leaves a good guess, given one that is not too small and a divisor whose top bit is set. Each
time round, `rest` grows by the divisor's top limb, which is at least half a limb's range, so twice round
is the most there is. -/
theorem refine_spec (g rest v1 v2 u2 : UInt64) (fuel : Nat) (top P Vl Ul U V : Nat)
    (hV : V = (v1.toNat * B + v2.toNat) * P + Vl) (hU : U = (top * B + u2.toNat) * P + Ul)
    (hv1 : 2147483648 ≤ v1.toNat) (hv1' : v1.toNat < B) (hv2 : v2.toNat < B) (hu2 : u2.toNat < B)
    (hVl : Vl < P) (hUl : Ul < P) (htop : top < (v1.toNat + 1) * B) (hUV : U < V * B)
    (hrest : rest.toNat < B) (hfuel : B ≤ rest.toNat + fuel * 2147483648)
    (hinv : g.toNat * v1.toNat + rest.toNat = top)
    (hlow : ∀ q, q * V ≤ U → q ≤ g.toNat) :
    GoodGuess (refine g rest v1 v2 u2 fuel).toNat U V := by
  induction fuel generalizing g rest with
  | zero => omega
  | succ fuel ih =>
    have m : (0xFFFFFFFF : UInt64).toNat = 4294967295 := rfl
    have hsum : (rest + v1).toNat = rest.toNat + v1.toNat := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    have small : ∀ q, q * V ≤ U → q < B := fun q hq =>
      Nat.lt_of_mul_lt_mul_right (a := V) (by rw [Nat.mul_comm B V]; omega)
    -- One step down, whichever test asked for it.
    have down : 0 < g.toNat → (∀ q, q * V ≤ U → q < g.toNat) →
        GoodGuess (if rest + v1 > 0xFFFFFFFF then g - 1 else refine (g - 1) (rest + v1) v1 v2 u2 fuel).toNat
          U V := by
      intro gpos strict
      have hg1 : (g - 1).toNat = g.toNat - 1 := by
        have := g.toNat_lt
        rw [UInt64.toNat_sub, show (1 : UInt64).toNat = 1 from rfl]; omega
      have hinv' : (g - 1).toNat * v1.toNat + (rest + v1).toNat = top := by
        obtain ⟨k, hk⟩ : ∃ k, g.toNat = k + 1 := ⟨g.toNat - 1, by omega⟩
        rw [hg1, hsum]
        rw [hk, Nat.add_mul, Nat.one_mul] at hinv
        rw [hk, Nat.add_sub_cancel]
        omega
      have hlow' : ∀ q, q * V ≤ U → q ≤ (g - 1).toNat := fun q hq => by
        have := strict q hq; omega
      by_cases over : rest + v1 > 0xFFFFFFFF
      · simp only [over, ↓reduceIte]
        have ov : B ≤ rest.toNat + v1.toNat := by
          have := UInt64.lt_iff_toNat_lt.mp over
          rw [m, hsum] at this; omega
        have kv : (g - 1).toNat * v1.toNat < B * v1.toNat := by
          rw [Nat.add_mul, Nat.one_mul] at htop
          rw [hsum] at hinv'
          rw [Nat.mul_comm B]
          omega
        have kB : (g - 1).toNat < B := Nat.lt_of_mul_lt_mul_right kv
        have prod : (g - 1).toNat * v2.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
        refine ⟨kB, hlow', ?_⟩
        subst hV hU
        exact guess_close _ _ _ _ _ _ _ _ _ hinv' (by rw [hsum]; omega) kB (by omega) hVl
      · simp only [over, ↓reduceIte]
        have nov : rest.toNat + v1.toNat < B := by
          have := mt UInt64.lt_iff_toNat_lt.mpr over
          rw [m, hsum] at this; omega
        exact ih (g - 1) (rest + v1) (by rw [hsum]; exact nov) (by rw [hsum]; omega) hinv' hlow'
    simp only [refine]
    by_cases big : 4294967295 < g.toNat
    · have hc : (decide (g > 0xFFFFFFFF) || decide (g * v2 > ((rest <<< 32) ||| u2))) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (UInt64.lt_iff_toNat_lt.mpr (by rw [m]; exact big))
      simp only [hc, ↓reduceIte]
      exact down (by omega) (fun q hq => by have := small q hq; omega)
    · have e1 : (g * v2).toNat = g.toNat * v2.toNat := by
        have : g.toNat * v2.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
        rw [UInt64.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : ((rest <<< 32) ||| u2).toNat = rest.toNat * B + u2.toNat := by
        have e : rest.toNat <<< 32 % 2 ^ 64 = rest.toNat <<< 32 :=
          Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega)
        rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, show (32 : UInt64).toNat % 64 = 32 from rfl, e,
          ← Nat.shiftLeft_add_eq_or_of_lt (show u2.toNat < 2 ^ 32 by omega), Nat.shiftLeft_eq]
      by_cases test : rest.toNat * B + u2.toNat < g.toNat * v2.toNat
      · have hc : (decide (g > 0xFFFFFFFF) || decide (g * v2 > ((rest <<< 32) ||| u2))) = true := by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          exact Or.inr (UInt64.lt_iff_toNat_lt.mpr (by rw [e1, e2]; exact test))
        simp only [hc, ↓reduceIte]
        have gpos : 0 < g.toNat := Nat.pos_of_ne_zero (fun z => by rw [z, Nat.zero_mul] at test; omega)
        refine down gpos (fun q hq => ?_)
        have tl : U < g.toNat * V := by
          subst hV hU; exact guess_too_large _ _ _ _ _ _ _ _ _ hinv test hUl
        exact Nat.lt_of_mul_lt_mul_right (a := V) (by omega)
      · have hc : (decide (g > 0xFFFFFFFF) || decide (g * v2 > ((rest <<< 32) ||| u2))) = false := by
          simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
          exact ⟨fun h => big (by have := UInt64.lt_iff_toNat_lt.mp h; rwa [m] at this),
            fun h => test (by have := UInt64.lt_iff_toNat_lt.mp h; rwa [e1, e2] at this)⟩
        simp only [hc, Bool.false_eq_true, ↓reduceIte]
        refine ⟨by omega, hlow, ?_⟩
        subst hV hU
        exact guess_close _ _ _ _ _ _ _ _ _ hinv (by omega) (by omega) (by omega) hVl

/-! ### D1: the shift that sets the divisor's top bit -/

theorem and_top_bit (x : Nat) (hx : x < B) : x &&& 2147483648 = 0 ↔ x < 2147483648 := by
  constructor
  · intro h
    apply Classical.byContradiction
    intro hge
    have t : x.testBit 31 = true := Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by omega)
    have both : (x &&& 2147483648).testBit 31 = true := by
      rw [Nat.testBit_and, t, show (2147483648 : Nat) = 2 ^ 31 from rfl, Nat.testBit_two_pow_self]; rfl
    rw [h] at both
    simp at both
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, show (2147483648 : Nat) = 2 ^ 31 from rfl, Nat.testBit_two_pow, Nat.zero_testBit]
    by_cases e : 31 = i
    · subst e; rw [Nat.testBit_lt_two_pow (by omega)]; rfl
    · simp [e]

/-- `topShift` finds the shift, below 32, that puts a limb's top bit at the top of the limb. -/
theorem topShift_spec (top s : UInt64) (fuel : Nat) (hpos : 0 < top.toNat)
    (hs : s.toNat ≤ 32) (hlt : top.toNat * 2 ^ s.toNat < B) (hfuel : 32 ≤ s.toNat + fuel) :
    (topShift top s fuel).toNat < 32
      ∧ 2147483648 ≤ top.toNat * 2 ^ (topShift top s fuel).toNat
      ∧ top.toNat * 2 ^ (topShift top s fuel).toNat < B := by
  induction fuel generalizing s with
  | zero =>
    have e : s.toNat = 32 := by omega
    rw [e] at hlt; omega
  | succ fuel ih =>
    have hshift : (top <<< s).toNat = top.toNat * 2 ^ s.toNat := by
      rw [UInt64.toNat_shiftLeft, Nat.mod_eq_of_lt (show s.toNat < 64 by omega), Nat.shiftLeft_eq,
        Nat.mod_eq_of_lt (by omega)]
    have hbit : ((top <<< s) &&& 0x80000000 == 0) = true ↔ top.toNat * 2 ^ s.toNat < 2147483648 := by
      rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_and, hshift,
        show (0x80000000 : UInt64).toNat = 2147483648 from rfl, show (0 : UInt64).toNat = 0 from rfl]
      exact and_top_bit _ hlt
    simp only [topShift]
    by_cases clear : top.toNat * 2 ^ s.toNat < 2147483648
    · simp only [hbit.mpr clear, ↓reduceIte]
      have s31 : s.toNat < 31 := by
        apply Classical.byContradiction
        intro h
        have h1 : 2 ^ 31 ≤ 2 ^ s.toNat := Nat.pow_le_pow_right (by decide) (by omega)
        have h2 : 1 * 2 ^ s.toNat ≤ top.toNat * 2 ^ s.toNat := Nat.mul_le_mul_right _ hpos
        omega
      have hs1 : (s + 1).toNat = s.toNat + 1 := by
        rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl]; exact Nat.mod_eq_of_lt (by omega)
      exact ih (s + 1) (by rw [hs1]; omega) (by rw [hs1, Nat.pow_succ, ← Nat.mul_assoc]; omega)
        (by rw [hs1]; omega)
    · have nb : ((top <<< s) &&& 0x80000000 == 0) = false := by
        cases hb : ((top <<< s) &&& 0x80000000 == 0)
        · rfl
        · exact absurd (hbit.mp hb) clear
      simp only [nb, Bool.false_eq_true, ↓reduceIte]
      have s32 : s.toNat < 32 := by
        apply Classical.byContradiction
        intro h
        have e : s.toNat = 32 := by omega
        rw [e] at hlt; omega
      exact ⟨s32, by omega, hlt⟩

/-! ### D2 to D7: one quotient limb at a time -/

/-- The limbs from `i` up are `k` limbs and then the limbs from `i + k` up. -/
theorem tail_split (a : Limbs) (i k : Nat) : ∃ low, low < B ^ k ∧ tail a i = low + B ^ k * tail a (i + k) := by
  induction k with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨low, hl, e⟩ := ih
    have d := digit_lt a (i + k)
    refine ⟨low + B ^ k * digit a (i + k), ?_, ?_⟩
    · have : B ^ k * digit a (i + k) ≤ B ^ k * 4294967295 := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.pow_succ]
      generalize B ^ k = P at *
      omega
    · rw [e, tail_step a (i + k), Nat.pow_succ, show i + (k + 1) = i + k + 1 from rfl]
      generalize B ^ k = P
      simp only [Nat.mul_add, Nat.mul_assoc]
      omega

theorem two_limbs (P Vl v2 v1 : Nat) : Vl + P * (v2 + B * (v1 + B * 0)) = (v1 * B + v2) * P + Vl := by
  have e : v1 * B + v2 = v2 + B * (v1 + B * 0) := by omega
  rw [e, Nat.mul_comm _ P]; omega

theorem three_limbs (P Ul u2 u1 u0 : Nat) :
    Ul + P * (u2 + B * (u1 + B * (u0 + B * 0))) = ((u0 * B + u1) * B + u2) * P + Ul := by
  have e : (u0 * B + u1) * B + u2 = u2 + B * (u1 + B * (u0 + B * 0)) := by omega
  rw [e, Nat.mul_comm _ P]; omega

/-- What is being divided into is less than the divisor times a limb's range, so its top two limbs are
bounded by the divisor's top limb. -/
theorem top_bound (top u2 Ul v1 v2 Vl P : Nat) (hv2 : v2 < B) (hVl : Vl < P)
    (h : (top * B + u2) * P + Ul < ((v1 * B + v2) * P + Vl) * B) : top < (v1 + 1) * B := by
  have a : top * (B * P) ≤ (top * B + u2) * P + Ul := by
    have := Nat.mul_le_mul_right P (Nat.le_add_right (top * B) u2)
    rw [← Nat.mul_assoc]; omega
  have b : (v1 * B + v2) * P + Vl < (v1 + 1) * B * P := by
    have t := Nat.mul_le_mul_right P (show v1 * B + v2 + 1 ≤ (v1 + 1) * B by omega)
    have e : (v1 * B + v2 + 1) * P = (v1 * B + v2) * P + P := by rw [Nat.add_mul, Nat.one_mul]
    rw [e] at t
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hVl _) t
  have c : ((v1 * B + v2) * P + Vl) * B < (v1 + 1) * B * P * B := (Nat.mul_lt_mul_right (by omega)).mpr b
  have d : (v1 + 1) * B * P * B = (v1 + 1) * B * (B * P) := by rw [Nat.mul_assoc, Nat.mul_comm P B]
  rw [d] at c
  exact Nat.lt_of_mul_lt_mul_right (a := B * P) (Nat.lt_of_le_of_lt a (Nat.lt_trans h c))

theorem step_remainder (Pj L U V : Nat) (hL : L < Pj) (hV : 0 < V) : L + Pj * (U % V) < V * Pj := by
  have h : U % V + 1 ≤ V := Nat.mod_lt _ hV
  have := Nat.mul_le_mul_left Pj h
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm Pj V] at this
  omega

theorem step_invariant (qv V Pj L U : Nat) :
    (qv + Pj * (U / V)) * V + (L + Pj * (U % V)) = qv * V + (L + Pj * U) := by
  have dm := Nat.div_add_mod U V
  have e : Pj * (U / V) * V + Pj * (U % V) = Pj * U := by
    rw [Nat.mul_assoc, ← Nat.mul_add, Nat.mul_comm (U / V) V, dm]
  rw [Nat.add_mul]; omega

/-- A good guess that could be taken off without going below zero was the quotient limb. -/
theorem step_exact (Pj L U V g u1 : Nat) (hL : L < Pj) (hV : 0 < V)
    (h : u1 + Pj * (g * V) = L + Pj * U) (hge : ∀ q, q * V ≤ U → q ≤ g) :
    g = U / V ∧ u1 = L + Pj * (U % V) := by
  have h1 : Pj * (g * V) < Pj * (U + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  have h2 : g * V ≤ U := Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left h1)
  have h3 : g ≤ U / V := (Nat.le_div_iff_mul_le hV).mpr h2
  have h4 : U / V ≤ g := hge _ (Nat.div_mul_le_self U V)
  have hg : g = U / V := by omega
  refine ⟨hg, ?_⟩
  have dm := Nat.div_add_mod U V
  have e : Pj * U = Pj * (g * V) + Pj * (U % V) := by
    rw [← Nat.mul_add, hg, Nat.mul_comm (U / V) V, dm]
  omega

/-- A good guess that went below zero was one too large, and putting the divisor back once leaves what the
quotient limb would have: the carry out of the top cancels the borrow. -/
theorem step_borrow (Pj L U V g u1 u2 Z c : Nat) (hL : L < Pj) (hV : 0 < V)
    (h1 : u1 + Pj * (g * V) = L + Pj * U + Z) (hu1 : u1 < Z)
    (hge : ∀ q, q * V ≤ U → q ≤ g) (hclose : g * V < U + V)
    (h2 : u2 + Z * c = u1 + Pj * V) (hc : c ≤ 1) (hu2 : u2 < Z) (hVZ : V * Pj ≤ Z) :
    g = U / V + 1 ∧ u2 = L + Pj * (U % V) := by
  have h3 : Pj * U < Pj * (g * V) := by omega
  have h4 : U < g * V := Nat.lt_of_mul_lt_mul_left h3
  have h5 : U / V ≤ g := hge _ (Nat.div_mul_le_self U V)
  have h6 : g ≠ U / V := fun e => by
    have := Nat.div_mul_le_self U V
    rw [← e] at this; omega
  have a : U < V * (U / V + 1) := Nat.lt_mul_div_succ U hV
  have b : (U / V + 2) * V = V * (U / V + 1) + V := by
    rw [Nat.mul_comm V, Nat.add_mul, Nat.add_mul]; omega
  have h7 : g * V < (U / V + 2) * V := by rw [b]; omega
  have h8 : g < U / V + 2 := Nat.lt_of_mul_lt_mul_right h7
  have hg : g = U / V + 1 := by omega
  refine ⟨hg, ?_⟩
  have dm := Nat.div_add_mod U V
  have e1 : Pj * (g * V) = Pj * (V * (U / V)) + Pj * V := by
    rw [hg, Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_comm (U / V) V]
  have e2 : Pj * U = Pj * (V * (U / V)) + Pj * (U % V) := by rw [← Nat.mul_add, dm]
  have rem := step_remainder Pj L U V hL hV
  have hc' : c = 0 ∨ c = 1 := by omega
  have fits := hVZ
  rcases hc' with rfl | rfl
  · rw [Nat.mul_zero] at h2; omega
  · rw [Nat.mul_one] at h2; omega

/-- The loop of long division. Going in, what is left of the dividend is less than the divisor moved up by
the quotient limbs still to come, and the quotient so far times the divisor, plus what is left, is the
dividend. Coming out, the same holds with nothing still to come: a quotient and a remainder. The divisor
has two limbs or more and its top bit set. -/
theorem divideLongLoop_value (v u q : Limbs) (j : Nat) (A : Nat)
    (hn : 2 ≤ v.size) (hnorm : 2147483648 ≤ digit v (v.size - 1))
    (hus : j + v.size ≤ u.size) (hqs : j ≤ q.size) (hqz : ∀ m, m < j → digit q m = 0)
    (hrem : value u < value v * B ^ j) (hinv : value q * value v + value u = A) :
    value (divideLongLoop v u q j).1 * value v + value (divideLongLoop v u q j).2 = A
      ∧ value (divideLongLoop v u q j).2 < value v := by
  induction j generalizing u q with
  | zero =>
    simp only [divideLongLoop]
    exact ⟨hinv, by simpa using hrem⟩
  | succ j ih =>
    obtain ⟨k, hk⟩ : ∃ k, v.size = k + 2 := ⟨v.size - 2, by omega⟩
    have i1 : v.size - 1 = k + 1 := by omega
    have i2 : v.size - 2 = k := by omega
    have i3 : j + v.size - 1 = j + k + 1 := by omega
    have i4 : j + v.size - 2 = j + k := by omega
    have i5 : j + v.size = j + k + 1 + 1 := by omega
    rw [i1] at hnorm
    have v1lt := digit_lt v (k + 1); have v2lt := digit_lt v k
    have u2lt := digit_lt u (j + k); have u1lt := digit_lt u (j + k + 1)
    have u0lt := digit_lt u (j + k + 1 + 1)
    have v1pos : 0 < digit v (k + 1) := by omega
    have Vpos : 0 < value v := by
      apply Nat.pos_of_ne_zero
      intro z
      rw [z, Nat.zero_mul] at hrem; omega
    -- The divisor, cut below its top two limbs.
    have hVs : value v = (digit v (k + 1) * B + digit v k) * B ^ k + lower v k := by
      have s := value_split v k
      rw [tail_step v k, tail_step v (k + 1), tail_of_le v (k + 1 + 1) (by omega)] at s
      rw [s]; exact two_limbs _ _ _ _
    have hVlt : value v < B ^ (k + 1 + 1) := by
      have := value_lt_pow v
      rwa [hk] at this
    -- What is being divided into: the limbs of `u` from `j` up, cut below their top three.
    have hsplit := value_split u j
    have hL := lower_lt u j
    have hUlt : tail u j < value v * B := by
      have h' := hrem
      rw [hsplit, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (value v), Nat.mul_assoc] at h'
      exact Nat.lt_of_mul_lt_mul_left (a := B ^ j) (by omega)
    have hZ : value u < B ^ (j + k + 1 + 1 + 1) := by
      have a : value v * B ^ (j + 1) < B ^ (k + 1 + 1) * B ^ (j + 1) :=
        (Nat.mul_lt_mul_right (Nat.pow_pos (by decide))).mpr hVlt
      rw [← Nat.pow_add, show k + 1 + 1 + (j + 1) = j + k + 1 + 1 + 1 by omega] at a
      omega
    have tz : tail u (j + k + 1 + 1 + 1) = 0 := tail_of_value_lt u _ hZ
    obtain ⟨Ul, hUl, eU⟩ := tail_split u j k
    have hUs : tail u j
        = ((digit u (j + k + 1 + 1) * B + digit u (j + k + 1)) * B + digit u (j + k)) * B ^ k + Ul := by
      rw [eU, tail_step u (j + k), tail_step u (j + k + 1), tail_step u (j + k + 1 + 1), tz]
      exact three_limbs _ _ _ _ _
    have htopb : digit u (j + k + 1 + 1) * B + digit u (j + k + 1) < (digit v (k + 1) + 1) * B := by
      have h' := hUlt
      rw [hUs, hVs] at h'
      exact top_bound _ _ _ _ _ _ _ v2lt (lower_lt v k) h'
    -- The step itself.
    simp only [divideLongLoop]
    rw [i1, i2, i3, i4, i5]
    generalize htop : (limb u (j + k + 1 + 1) <<< 32) ||| limb u (j + k + 1) = top64
    have htopN : top64.toNat = digit u (j + k + 1 + 1) * B + digit u (j + k + 1) := by
      subst htop
      rw [two_limbs_word _ _ (by rw [limb_toNat]; exact u0lt) (by rw [limb_toNat]; exact u1lt), limb_toNat,
        limb_toNat]
    generalize hg : refine (top64 / limb v (k + 1)) (top64 % limb v (k + 1)) (limb v (k + 1)) (limb v k)
      (limb u (j + k)) 4 = g
    have good : GoodGuess g.toNat (tail u j) (value v) := by
      rw [← hg]
      refine refine_spec _ _ _ _ _ 4 (digit u (j + k + 1 + 1) * B + digit u (j + k + 1)) (B ^ k) (lower v k) Ul
        (tail u j) (value v) ?_ ?_ ?_ ?_ ?_ ?_ (lower_lt v k) hUl ?_ hUlt ?_ ?_ ?_ ?_
      · rw [limb_toNat, limb_toNat]; exact hVs
      · rw [limb_toNat]; exact hUs
      · rw [limb_toNat]; exact hnorm
      · rw [limb_toNat]; exact v1lt
      · rw [limb_toNat]; exact v2lt
      · rw [limb_toNat]; exact u2lt
      · rw [limb_toNat]; exact htopb
      · rw [UInt64.toNat_mod, limb_toNat, htopN]
        have := Nat.mod_lt (digit u (j + k + 1 + 1) * B + digit u (j + k + 1)) v1pos
        omega
      · omega
      · rw [UInt64.toNat_div, UInt64.toNat_mod, limb_toNat, htopN]
        exact Nat.div_add_mod' _ _
      · intro q hq
        rw [UInt64.toNat_div, limb_toNat, htopN]
        rw [hVs, hUs] at hq
        have a := mul_top_le q _ _ _ _ _ hUl hq
        have b := mul_top_le q _ _ _ _ _ u2lt a
        exact (Nat.le_div_iff_mul_le v1pos).mpr b
    obtain ⟨gB, glow, gclose⟩ := good
    have hVZ : value v * B ^ j ≤ B ^ (j + v.size + 1) := by
      have a : value v * B ^ j ≤ B ^ (k + 1 + 1) * B ^ j := Nat.mul_le_mul_right _ (Nat.le_of_lt hVlt)
      rw [← Nat.pow_add] at a
      exact Nat.le_trans a (Nat.pow_le_pow_right (by decide) (by omega))
    have hRZ : value u < B ^ (j + v.size + 1) := by
      rw [show j + v.size + 1 = j + k + 1 + 1 + 1 by omega]; exact hZ
    have tzu : tail u (j + v.size + 1) = 0 := tail_of_value_lt u _ hRZ
    -- Whichever way the step goes, it leaves the quotient limb written and the remainder in `u`.
    have finish : ∀ (u' : Limbs) (d : UInt32), u'.size = u.size →
        value u' = lower u j + B ^ j * (tail u j % value v) → d.toNat = tail u j / value v →
        value (divideLongLoop v u' (q.setIfInBounds j d) j).1 * value v
            + value (divideLongLoop v u' (q.setIfInBounds j d) j).2 = A
          ∧ value (divideLongLoop v u' (q.setIfInBounds j d) j).2 < value v := by
      intro u' d hsize hval hd
      have written := value_set q j d (by omega)
      rw [hqz j (Nat.lt_succ_self j), hd] at written
      refine ih u' (q.setIfInBounds j d) (by omega) (by simp; omega)
        (fun m hm => by rw [digit_set_ne _ _ _ _ (by omega)]; exact hqz m (by omega)) ?_ ?_
      · rw [hval]; exact step_remainder _ _ _ _ hL Vpos
      · have e : value (q.setIfInBounds j d) = value q + B ^ j * (tail u j / value v) := by
          simpa using written
        rw [e, hval, step_invariant, ← hsplit]; exact hinv
    have tv := takeLoop_value v g j 0 0 0 u gB (by decide) (by decide) (Nat.zero_le _) (by omega)
    have tt := takeLoop_tail v g j 0 0 0 u (j + v.size + 1) (by omega)
    have ts := takeLoop_size v g j 0 0 0 u
    generalize ht : takeLoop v g j 0 0 0 u = res at tv tt ts ⊢
    obtain ⟨u1, below⟩ := res
    dsimp only at tv tt ts ⊢
    simp only [Nat.zero_add, tail_zero, show (0 : UInt64).toNat = 0 from rfl] at tv
    by_cases hb : below = 0
    · subst hb
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      have e := tv.1
      rw [show (0 : UInt64).toNat = 0 from rfl, Nat.mul_zero, Nat.add_zero, hsplit] at e
      obtain ⟨eg, eu⟩ := step_exact _ _ _ _ _ _ hL Vpos e glow
      exact finish u1 g.toUInt32 ts eu (by rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt gB]; exact eg)
    · have b1 : below.toNat = 1 := by
        have nz : below.toNat ≠ 0 := fun z => hb (UInt64.toNat_inj.mp (by rw [z]; rfl))
        have := tv.2
        omega
      simp only [bne_iff_ne, ne_eq, hb, not_false_eq_true, ↓reduceIte]
      have e := tv.1
      rw [b1, Nat.mul_one, hsplit] at e
      have u1Z : value u1 < B ^ (j + v.size + 1) := value_lt_of_tail u1 _ (by rw [tt]; exact tzu)
      obtain ⟨c, hc, pb⟩ := putBackLoop_value v j 0 0 u1 (by decide) (Nat.zero_le _) (by omega)
      simp only [Nat.zero_add, tail_zero, show (0 : UInt64).toNat = 0 from rfl] at pb
      have pt := putBackLoop_tail v j 0 0 u1 (j + v.size + 1) (by omega)
      have u2Z : value (putBackLoop v j 0 0 u1) < B ^ (j + v.size + 1) :=
        value_lt_of_tail _ _ (by rw [pt, tt]; exact tzu)
      obtain ⟨eg, eu⟩ := step_borrow _ _ _ _ _ _ _ _ _ hL Vpos e u1Z glow gclose pb hc u2Z hVZ
      have g1 : (g - 1).toUInt32.toNat = tail u j / value v := by
        have gpos : 0 < g.toNat := by rw [eg]; exact Nat.succ_pos _
        have small : tail u j / value v < B := by
          have h := gB
          rw [eg] at h
          exact Nat.lt_of_succ_lt h
        rw [UInt64.toNat_toUInt32, toNat_pred g gpos, eg, Nat.add_sub_cancel]
        exact Nat.mod_eq_of_lt small
      exact finish _ _ (by rw [putBackLoop_size]; exact ts) eu g1

/-! ### D1 and D8: the shifts around the loop, and the whole of long division -/

theorem shiftLeftLoop_size (a : Limbs) (bits : UInt64) (i : Nat) (carry : UInt64) (r : Limbs) :
    (shiftLeftLoop a bits i carry r).size = r.size + (a.size - i) + 1 := by
  fun_induction shiftLeftLoop a bits i carry r with
  | case1 i carry r h t ih => rw [ih, Array.size_push]; omega
  | case2 i carry r h => rw [Array.size_push]; omega

theorem shiftLeft_size (a : Limbs) (whole : Nat) (bits : UInt64) :
    (shiftLeft a whole bits).size = whole + a.size + 1 := by
  rw [shiftLeft, shiftLeftLoop_size]; simp [zeros]

/-- Long division by two limbs or more: the quotient rounded down and the remainder. The divisor has no zero
limb on top and the dividend has at least as many limbs. -/
theorem divideLong_value (a b : Limbs) (hn : 2 ≤ b.size) (hab : b.size ≤ a.size) (tb : Trimmed b) :
    value (divideLong a b).1 = value a / value b ∧ value (divideLong a b).2 = value a % value b := by
  obtain ⟨k, hk⟩ : ∃ k, b.size = k + 1 := ⟨b.size - 1, by omega⟩
  have i1 : b.size - 1 = k := by omega
  have btop : digit b k ≠ 0 := by
    rcases tb with z | nz
    · omega
    · rwa [i1] at nz
  have blt := digit_lt b k
  have z : (0 : UInt64).toNat = 0 := rfl
  have hs := topShift_spec (limb b k) 0 32 (by rw [limb_toNat]; omega) (by simp)
    (by rw [z, limb_toNat, Nat.pow_zero, Nat.mul_one]; exact blt) (by simp)
  rw [limb_toNat] at hs
  simp only [divideLong]
  rw [i1]
  generalize topShift (limb b k) 0 32 = s at hs ⊢
  obtain ⟨s32, slo, shi⟩ := hs
  have Epos : 0 < 2 ^ s.toNat := Nat.two_pow_pos _
  have EF : 2 ^ (32 - s.toNat) * 2 ^ s.toNat = B := by
    rw [← Nat.pow_add, show 32 - s.toNat + s.toNat = 32 by omega]
  have hbs : value b = lower b k + B ^ k * digit b k := by
    have sp := value_split b k
    rw [tail_step b k, tail_of_le b (k + 1) (by omega)] at sp
    simpa using sp
  have hbl := lower_lt b k
  -- The divisor moved up: its top bit is set, and it still fits its limbs.
  have hVhi : value b * 2 ^ s.toNat < B ^ (k + 1) := by
    have d1 : digit b k < 2 ^ (32 - s.toNat) :=
      Nat.lt_of_mul_lt_mul_right (a := 2 ^ s.toNat) (by rw [EF]; exact shi)
    have d2 : (digit b k + 1) * 2 ^ s.toNat ≤ B := by rw [← EF]; exact Nat.mul_le_mul_right _ d1
    have d3 : value b + 1 ≤ B ^ k * (digit b k + 1) := by rw [hbs, Nat.mul_add, Nat.mul_one]; omega
    have d4 : (value b + 1) * 2 ^ s.toNat ≤ B ^ k * B :=
      calc (value b + 1) * 2 ^ s.toNat ≤ B ^ k * (digit b k + 1) * 2 ^ s.toNat := Nat.mul_le_mul_right _ d3
        _ = B ^ k * ((digit b k + 1) * 2 ^ s.toNat) := Nat.mul_assoc _ _ _
        _ ≤ B ^ k * B := Nat.mul_le_mul_left _ d2
    rw [Nat.pow_succ]
    rw [Nat.add_mul, Nat.one_mul] at d4
    omega
  have hVlo : 2147483648 * B ^ k ≤ value b * 2 ^ s.toNat :=
    calc 2147483648 * B ^ k ≤ digit b k * 2 ^ s.toNat * B ^ k := Nat.mul_le_mul_right _ slo
      _ = B ^ k * digit b k * 2 ^ s.toNat := by
        rw [Nat.mul_comm (digit b k * 2 ^ s.toNat), Nat.mul_assoc]
      _ ≤ value b * 2 ^ s.toNat := Nat.mul_le_mul_right _ (by rw [hbs]; omega)
  have hsb : value (shiftLeft b 0 s) = value b * 2 ^ s.toNat := by rw [shiftLeft_value _ _ _ s32]; simp
  have hsbsize : (shiftLeft b 0 s).size = k + 1 + 1 := by rw [shiftLeft_size, hk]; omega
  have hsbtop : (shiftLeft b 0 s).getD ((shiftLeft b 0 s).size - 1) 0 = 0 := by
    have t0 : tail (shiftLeft b 0 s) (k + 1) = 0 := tail_of_value_lt _ _ (by rw [hsb]; exact hVhi)
    have st := tail_step (shiftLeft b 0 s) (k + 1)
    rw [t0] at st
    have dz : digit (shiftLeft b 0 s) (k + 1) = 0 := by omega
    rw [hsbsize, Nat.add_sub_cancel]
    exact UInt32.toNat_inj.mp (show ((shiftLeft b 0 s).getD (k + 1) 0).toNat = (0 : UInt32).toNat from dz)
  generalize hvdef : (shiftLeft b 0 s).pop = v
  have hv : value v = value b * 2 ^ s.toNat := by
    rw [← hvdef, value_pop _ (by rw [hsbsize]; omega) hsbtop, hsb]
  have hvsize : v.size = k + 1 := by rw [← hvdef, Array.size_pop, hsbsize, Nat.add_sub_cancel]
  have hvtop : 2147483648 ≤ digit v (v.size - 1) := by
    rw [hvsize, Nat.add_sub_cancel]
    have st := tail_step v k
    rw [tail_of_le v (k + 1) (by omega), tail_eq_div] at st
    have big : 2147483648 ≤ value v / B ^ k :=
      (Nat.le_div_iff_mul_le (Nat.pow_pos (by omega))).mpr (by rw [hv]; exact hVlo)
    omega
  -- The dividend moved up by as much, and one limb longer.
  have hsa : value (shiftLeft a 0 s) = value a * 2 ^ s.toNat := by rw [shiftLeft_value _ _ _ s32]; simp
  have hsasize : (shiftLeft a 0 s).size = a.size + 1 := by rw [shiftLeft_size]; omega
  have hrem : value (shiftLeft a 0 s) < value v * B ^ (a.size - b.size + 1) := by
    have e1 : 2 ^ s.toNat ≤ 2147483648 := Nat.pow_le_pow_right (by omega) (show s.toNat ≤ 31 by omega)
    have e2 : value a * 2 ^ s.toNat < B ^ a.size * 2 ^ s.toNat :=
      (Nat.mul_lt_mul_right Epos).mpr (value_lt_pow a)
    have e3 : B ^ a.size * 2 ^ s.toNat ≤ B ^ a.size * 2147483648 := Nat.mul_le_mul_left _ e1
    have e4 : B ^ a.size * 2147483648 = 2147483648 * B ^ k * B ^ (a.size - b.size + 1) := by
      rw [Nat.mul_assoc, ← Nat.pow_add, show k + (a.size - b.size + 1) = a.size by omega, Nat.mul_comm]
    have e5 : 2147483648 * B ^ k * B ^ (a.size - b.size + 1) ≤ value v * B ^ (a.size - b.size + 1) :=
      Nat.mul_le_mul_right _ (by rw [hv]; exact hVlo)
    rw [hsa]
    exact Nat.lt_of_lt_of_le e2 (Nat.le_trans e3 (by rw [e4]; exact e5))
  have loop := divideLongLoop_value v (shiftLeft a 0 s) (zeros (a.size - b.size + 1)) (a.size - b.size + 1)
    (value a * 2 ^ s.toNat) (by omega) hvtop (by rw [hvsize, hsasize]; omega) (by simp [zeros])
    (fun m _ => digit_zeros _ m) hrem (by rw [value_zeros, Nat.zero_mul, Nat.zero_add, hsa])
  generalize divideLongLoop v (shiftLeft a 0 s) (zeros (a.size - b.size + 1)) (a.size - b.size + 1) = res
    at loop ⊢
  obtain ⟨qq, uu⟩ := res
  dsimp only at loop ⊢
  obtain ⟨linv, lrem⟩ := loop
  rw [hv] at linv lrem
  have whole : value uu + value b * 2 ^ s.toNat * value qq = value a * 2 ^ s.toNat := by
    rw [Nat.add_comm, Nat.mul_comm (value b * 2 ^ s.toNat) (value qq)]; exact linv
  have both := (Nat.div_mod_unique (Nat.lt_of_le_of_lt (Nat.zero_le _) lrem)).mpr ⟨whole, lrem⟩
  rw [Nat.mul_div_mul_right _ _ Epos, Nat.mul_mod_mul_right] at both
  refine ⟨both.1.symm, ?_⟩
  have ulim : value uu < B ^ b.size := by rw [hk]; exact Nat.lt_trans lrem hVhi
  rw [shiftRight_value _ _ _ _ s32 ulim, ← both.2]
  simp only [Nat.mul_zero, Nat.zero_add]
  exact Nat.mul_div_cancel _ Epos

/-- `divide` gives the quotient rounded down and the remainder, for any dividend and any divisor that is not
zero and has no zero limb on top. -/
theorem divide_value (a b : Limbs) (tb : Trimmed b) (hz : value b ≠ 0) :
    value (divide a b).1 = value a / value b ∧ value (divide a b).2 = value a % value b := by
  by_cases short : a.size < b.size
  · exact divide_value_shorter a b short tb
  · by_cases one : b.size = 1
    · exact divide_value_single a b one hz
    · have some : b.size ≠ 0 := fun e => hz (by
        have := value_lt_pow b
        rw [e] at this
        simpa using this)
      have e : divide a b = divideLong a b := by simp [divide, short, one]
      rw [e]
      exact divideLong_value a b (by omega) (by omega) tb

/-- Division of natural numbers, rounding down; by zero it gives zero, as Lean's does. -/
theorem natDiv_value (a b : Limbs) (tb : Trimmed b) : value (natDiv a b) = value a / value b := by
  by_cases e : b.size = 0
  · have zero : value b = 0 := by
      have := value_lt_pow b
      rw [e] at this
      simpa using this
    have e' : natDiv a b = Array.mkEmpty 0 := by simp [natDiv, e]
    rw [e', zero, Nat.div_zero]
    rfl
  · have pos := pow_le_value b e tb
    have one : 0 < B ^ (b.size - 1) := Nat.pow_pos (by omega)
    have e' : natDiv a b = (divide a b).1 := by simp [natDiv, e]
    rw [e']
    exact (divide_value a b tb (by omega)).1

/-- The remainder of natural numbers, for a divisor that is not zero. -/
theorem natMod_value (a b : Limbs) (tb : Trimmed b) (hz : value b ≠ 0) :
    value (natMod a b) = value a % value b :=
  (divide_value a b tb hz).2

/-! ## Powers -/

theorem value_one : value (one ()) = 1 := by simp [one, low, value, valueList]

theorem powerLoop_value (power result : Limbs) (exponent : USize) (fuel : Nat) (h : exponent.toNat < 2 ^ fuel) :
    value (powerLoop power result exponent fuel) = value result * value power ^ exponent.toNat := by
  induction fuel generalizing power result exponent with
  | zero =>
    have z : exponent.toNat = 0 := by simpa using h
    simp [powerLoop, z]
  | succ fuel ih =>
    have one : (1 : USize).toNat = 1 := USize.toNat_ofNat_of_lt_32 (by decide)
    have half : (exponent >>> 1).toNat = exponent.toNat / 2 := by
      have : (1 : USize).toNat % System.Platform.numBits = 1 := by
        rw [one]; rcases System.Platform.numBits_eq with e | e <;> rw [e]
      rw [USize.toNat_shiftRight, this, Nat.shiftRight_eq_div_pow, Nat.pow_one]
    have bit : (exponent &&& 1).toNat = exponent.toNat % 2 := by
      rw [USize.toNat_and, one, Nat.and_one_is_mod]
    have step : value power ^ exponent.toNat =
        value power ^ (exponent.toNat % 2) * (value power * value power) ^ (exponent.toNat / 2) := by
      conv => lhs; rw [← Nat.mod_add_div exponent.toNat 2]
      rw [Nat.pow_add, Nat.pow_mul, Nat.pow_two]
    have hr : value (if exponent &&& 1 != 0 then trim (mul result power) else result) =
        value result * value power ^ (exponent.toNat % 2) := by
      by_cases o : exponent &&& 1 = 0
      · have : exponent.toNat % 2 = 0 := by rw [← bit, o]; rfl
        simp [o, this]
      · have : (exponent &&& 1).toNat ≠ 0 := fun e => o (USize.toNat_inj.mp (by simpa using e))
        have : exponent.toNat % 2 = 1 := by omega
        simp [o, this, trim_value, mul_value]
    unfold powerLoop
    by_cases z : exponent = 0
    · simp [z]
    · by_cases z2 : exponent >>> 1 = 0
      · have : exponent.toNat / 2 = 0 := by rw [← half, z2]; rfl
        simp only [beq_iff_eq, z, z2, ↓reduceIte]
        rw [hr, step, this, Nat.pow_zero, Nat.mul_one]
      · simp only [beq_iff_eq, z, z2, ↓reduceIte]
        rw [ih _ _ _ (by rw [half, Nat.pow_succ] at *; omega), hr, trim_value, mul_value, half, step, Nat.mul_assoc]

/-- The limbs `power` returns are those of the power, for any exponent a machine word holds. Anything to
the power 0 is 1. -/
theorem power_value (a : Limbs) (exponent : USize) : value (power a exponent) = value a ^ exponent.toNat := by
  rw [power, powerLoop_value _ _ _ _ (USize.toNat_lt exponent), value_one, Nat.one_mul]

/-! ## Integers -/

/-- The integer with this sign and these limbs. -/
def intOf (negative : Bool) (limbs : Limbs) : Int := if negative then -(value limbs : Int) else value limbs

/-- The integer a result is: its limbs, then one more element that is not zero if it is below zero. -/
def signedValue (r : Limbs) : Int := intOf (r.getD (r.size - 1) 0 != 0) r.pop

theorem signedValue_signed (negative : Bool) (limbs : Limbs) :
    signedValue (signed negative limbs) = intOf negative limbs := by
  cases negative <;> simp [signedValue, signed, low, Array.getD]

/-- A sign as the runtime passes it: 0, or 1 for a number below zero. -/
def IsSign (s : UInt8) : Prop := s = 0 ∨ s = 1

theorem intMul_value (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn) :
    signedValue (intMul an a bn b) = intOf (an != 0) a * intOf (bn != 0) b := by
  rw [intMul, signedValue_signed]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp [intOf, mul_value, Int.natCast_mul, Int.mul_neg, Int.neg_mul]

/-- Signed addition, on numbers with no zero limb on top: `compare` has to say which is larger. -/
theorem intAdd_value (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn)
    (ta : Trimmed a) (tb : Trimmed b) :
    signedValue (intAdd an a bn b) = intOf (an != 0) a + intOf (bn != 0) b := by
  have same : ∀ s : UInt8, signedValue (intAdd s a s b) = intOf (s != 0) a + intOf (s != 0) b := by
    intro s
    simp only [intAdd, beq_self_eq_true, ↓reduceIte, signedValue_signed, intOf, add_value]
    split <;> omega
  have differ : ∀ s t : UInt8, (s == t) = false →
      signedValue (intAdd s a t b) =
        if value a < value b then intOf (t != 0) (sub b a)
        else if value a = value b then 0 else intOf (s != 0) (sub a b) := by
    intro s t h
    simp only [intAdd, h, Bool.false_eq_true, ↓reduceIte, compare_order a b ta tb, order]
    by_cases h1 : value a < value b
    · simp only [h1, ↓reduceIte, show ((0 : UInt8) == 1) = false from rfl, show ((0 : UInt8) == 2) = false from rfl,
        Bool.false_eq_true, signedValue_signed]
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, show ((1 : UInt8) == 1) = true from rfl, signedValue_signed]
        simp [intOf, value, valueList]
      · simp only [h1, h2, ↓reduceIte, show ((2 : UInt8) == 1) = false from rfl, show ((2 : UInt8) == 2) = true from rfl,
          Bool.false_eq_true, signedValue_signed]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact same 0
  · rw [differ 0 1 rfl]
    by_cases h1 : value a < value b
    · have := sub_value b a (by omega)
      simp only [h1, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl, show ((0 : UInt8) != 0) = false from rfl,
        Bool.false_eq_true, this]
      omega
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true]
        omega
      · have := sub_value a b (by omega)
        simp only [h1, h2, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, this]
        omega
  · rw [differ 1 0 rfl]
    by_cases h1 : value a < value b
    · have := sub_value b a (by omega)
      simp only [h1, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl, show ((0 : UInt8) != 0) = false from rfl,
        Bool.false_eq_true, this]
      omega
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true]
        omega
      · have := sub_value a b (by omega)
        simp only [h1, h2, ↓reduceIte, intOf, show ((1 : UInt8) != 0) = true from rfl,
          show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, this]
        omega
  · exact same 1

/-- 0, 1 or 2 as the first integer is less than, equal to or greater than the second. -/
def intOrder (x y : Int) : UInt8 := if x < y then 0 else if x = y then 1 else 2

/-- Signed comparison, on numbers with no zero limb on top. A number passed as below zero is not zero:
the runtime has no "minus zero", and `intCompare` would call it less than zero. -/
theorem intCompare_order (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn)
    (ta : Trimmed a) (tb : Trimmed b) (za : an = 1 → value a ≠ 0) (zb : bn = 1 → value b ≠ 0) :
    intCompare an a bn b = intOrder (intOf (an != 0) a) (intOf (bn != 0) b) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · simp only [intCompare, show ((0 : UInt8) != 0) = false from rfl, Bool.false_eq_true, ↓reduceIte,
      compare_order a b ta tb, order, intOrder, intOf]
    by_cases h1 : value a < value b
    · have : (value a : Int) < value b := by omega
      simp [h1, this]
    · by_cases h2 : value a = value b
      · simp [h2]
      · have h3 : ¬ (value a : Int) < value b := by omega
        have h4 : (value a : Int) ≠ value b := by omega
        simp [h1, h2, h3, h4]
  · have := zb rfl
    have h3 : ¬ (value a : Int) < -(value b : Int) := by omega
    have h4 : (value a : Int) ≠ -(value b : Int) := by omega
    simp [intCompare, intOrder, intOf, h3, h4]
  · have := za rfl
    have h3 : -(value a : Int) < (value b : Int) := by omega
    simp [intCompare, intOrder, intOf, h3]
  · simp only [intCompare, show ((1 : UInt8) != 1) = false from rfl, show ((1 : UInt8) != 0) = true from rfl,
      Bool.false_eq_true, ↓reduceIte, compare_order a b ta tb, order, intOrder, intOf]
    by_cases h1 : value a < value b
    · have h3 : ¬ -(value a : Int) < -(value b : Int) := by omega
      have h4 : -(value a : Int) ≠ -(value b : Int) := by omega
      simp only [h1, ↓reduceIte, h3, h4]
      rfl
    · by_cases h2 : value a = value b
      · simp only [h2, Nat.lt_irrefl, Int.lt_irrefl, ↓reduceIte]
        rfl
      · have h3 : -(value a : Int) < -(value b : Int) := by omega
        simp only [h1, h2, ↓reduceIte, h3]
        rfl

/-! ### Signed division

`Int`'s own division: the remainder is never negative, and dividing by zero gives zero. -/

/-- `trim` leaves no zero limb on top. -/
theorem trim_trimmed (a : Limbs) : Trimmed (trim a) := by
  fun_induction trim a with
  | case1 a h => exact Or.inl h
  | case2 a h top ih => exact ih
  | case3 a h top =>
    exact Or.inr (fun z => top (beq_iff_eq.mpr
      (UInt32.toNat_inj.mp (show (a.getD (a.size - 1) 0).toNat = (0 : UInt32).toNat from z))))

/-- What `trim` leaves has no limbs exactly when the number is zero. -/
theorem trim_size_eq_zero (a : Limbs) : (trim a).size = 0 ↔ value a = 0 := by
  constructor
  · intro h
    have := value_lt_pow (trim a)
    rw [h, trim_value] at this
    simpa using this
  · intro h
    apply Classical.byContradiction
    intro ne
    have := pow_le_value (trim a) ne (trim_trimmed a)
    have pos : 0 < B ^ ((trim a).size - 1) := Nat.pow_pos (by omega)
    rw [trim_value, h] at this
    omega

/-- Dividing a number below zero by one above it, from the quotient and remainder of the two without their
signs: if anything is left over the quotient is one further from zero, and the remainder is what is missing
from the divisor. -/
theorem neg_ediv_emod (n D : Nat) (hD : 0 < D) :
    (-(n : Int)) / (D : Int) = -((n / D + (if n % D = 0 then 0 else 1) : Nat) : Int) ∧
    (-(n : Int)) % (D : Int) = ((if n % D = 0 then 0 else D - n % D : Nat) : Int) := by
  have dm : (D : Int) * ((n / D : Nat) : Int) + ((n % D : Nat) : Int) = (n : Int) := by
    exact_mod_cast Nat.div_add_mod n D
  have lt : n % D < D := Nat.mod_lt _ hD
  apply (Int.ediv_emod_unique (Int.natCast_pos.mpr hD)).mpr
  by_cases h : n % D = 0
  · simp only [h, ↓reduceIte, Nat.add_zero]
    rw [h] at dm
    refine ⟨?_, by omega, by omega⟩
    rw [Int.mul_neg]; omega
  · simp only [h, ↓reduceIte]
    refine ⟨?_, by omega, by omega⟩
    rw [Int.natCast_sub (Nat.le_of_lt lt), Int.natCast_add, Int.mul_neg, Int.mul_add]
    simp only [Int.natCast_one, Int.mul_one]
    omega

/-- Signed division, as Lean's `Int` divides: the remainder is never negative, and dividing by zero gives
zero. The divisor has no zero limb on top. -/
theorem intEdiv_value (an : UInt8) (a : Limbs) (bn : UInt8) (b : Limbs) (ha : IsSign an) (hb : IsSign bn)
    (tb : Trimmed b) : signedValue (intEdiv an a bn b) = intOf (an != 0) a / intOf (bn != 0) b := by
  by_cases e : b.size = 0
  · have zero : value b = 0 := by
      have := value_lt_pow b
      rw [e] at this
      simpa using this
    have r : intEdiv an a bn b = signed false (Array.mkEmpty 0) := by simp [intEdiv, e]
    have d0 : intOf (bn != 0) b = 0 := by simp [intOf, zero]
    rw [r, signedValue_signed, d0, Int.ediv_zero]
    rfl
  · have pos : 0 < value b := by
      have := pow_le_value b e tb
      have one : 0 < B ^ (b.size - 1) := Nat.pow_pos (by omega)
      omega
    obtain ⟨hq, hr⟩ := divide_value a b tb (by omega)
    have nonneg := Int.natCast_ediv (value a) (value b)
    have neg := (neg_ediv_emod (value a) (value b) pos).1
    generalize hd : divide a b = d at hq hr
    obtain ⟨q, r⟩ := d
    dsimp only at hq hr
    have body : ∃ q', intEdiv an a bn b = signed (an != bn) q' ∧
        value q' = value a / value b + (if an = 1 ∧ value a % value b ≠ 0 then 1 else 0) := by
      refine ⟨if an != 0 && (trim r).size != 0 then add q (one ()) else q, ?_, ?_⟩
      · simp only [intEdiv, hd]; simp [e]
      · rcases ha with rfl | rfl
        · simp [hq]
        · by_cases rem0 : value a % value b = 0
          · have t0 : (trim r).size = 0 := (trim_size_eq_zero r).mpr (by rw [hr]; exact rem0)
            simp [t0, rem0, hq]
          · have t1 : (trim r).size ≠ 0 := fun h => rem0 (by rw [← hr]; exact (trim_size_eq_zero r).mp h)
            simp [t1, rem0, hq, add_value, value_one]
    obtain ⟨q', hbody, vq'⟩ := body
    rw [hbody, signedValue_signed]
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · have v : value q' = value a / value b := by simpa using vq'
      show (value q' : Int) = (value a : Int) / (value b : Int)
      rw [v]; exact nonneg
    · have v : value q' = value a / value b := by simpa using vq'
      show -(value q' : Int) = (value a : Int) / -(value b : Int)
      rw [v, Int.ediv_neg, nonneg]
    · have v : value q' = value a / value b + (if value a % value b = 0 then 0 else 1) := by
        rw [vq']; by_cases r0 : value a % value b = 0 <;> simp [r0]
      show -(value q' : Int) = -(value a : Int) / (value b : Int)
      rw [v]; exact neg.symm
    · have v : value q' = value a / value b + (if value a % value b = 0 then 0 else 1) := by
        rw [vq']; by_cases r0 : value a % value b = 0 <;> simp [r0]
      show (value q' : Int) = -(value a : Int) / -(value b : Int)
      rw [v, Int.ediv_neg, neg, Int.neg_neg]

/-- The remainder of signed division, which is never negative and does not depend on the divisor's sign.
The divisor is not zero and has no zero limb on top. -/
theorem intEmod_value (an : UInt8) (a b : Limbs) (bneg : Bool) (ha : IsSign an) (tb : Trimmed b)
    (hz : value b ≠ 0) : signedValue (intEmod an a b) = intOf (an != 0) a % intOf bneg b := by
  have pos : 0 < value b := by omega
  have hr := (divide_value a b tb hz).2
  have vr : value (trim (divide a b).2) = value a % value b := by rw [trim_value, hr]
  have lt : value a % value b < value b := Nat.mod_lt _ pos
  have dsign : ∀ x : Int, x % intOf bneg b = x % (value b : Int) := by
    intro x
    cases bneg
    · rfl
    · exact Int.emod_neg _ _
  rw [dsign]
  simp only [intEmod]
  rw [signedValue_signed]
  rcases ha with rfl | rfl
  · simp only [show ((0 : UInt8) != 0) = false from rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    show (value (trim (divide a b).2) : Int) = (value a : Int) % (value b : Int)
    rw [vr]; exact Int.natCast_emod _ _
  · have neg := (neg_ediv_emod (value a) (value b) pos).2
    simp only [show ((1 : UInt8) != 0) = true from rfl, Bool.true_and]
    by_cases r0 : value a % value b = 0
    · have t0 : (trim (divide a b).2).size = 0 := (trim_size_eq_zero _).mpr (by rw [hr]; exact r0)
      simp only [t0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      show (value (trim (divide a b).2) : Int) = -(value a : Int) % (value b : Int)
      rw [vr, neg]; simp [r0]
    · have t1 : (trim (divide a b).2).size ≠ 0 := fun h =>
        r0 (by rw [← hr]; exact (trim_size_eq_zero _).mp h)
      simp only [bne_iff_ne, ne_eq, t1, not_false_eq_true, ↓reduceIte]
      show (value (sub b (trim (divide a b).2)) : Int) = -(value a : Int) % (value b : Int)
      rw [sub_value _ _ (by rw [vr]; omega), vr, neg]; simp [r0]

end Runtime.Big
