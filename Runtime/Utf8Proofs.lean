import Runtime.Utf8
import Std.Tactic.BVDecide

/-! # The rules of UTF-8, against the standard's table

`Runtime/Utf8.lean` works in masks and shifts. This states UTF-8 the way the standard does (RFC 3629,
section 3: four ranges of characters, and for each how many bytes and what goes in them) in plain
arithmetic, and proves for every character and every four bytes that the runtime's rules are those. Nothing
here runs; no image imports it.

The questions about bytes are finite, and are settled by `bv_decide`, which hands them to a SAT solver and
checks its answer with compiled code, recorded as an axiom of its own. So these theorems trust the compiler
that ran that check, beyond Lean's three standard axioms, as the mask proofs in `Mini/WordProofs.lean` do. -/

namespace Runtime.Utf8

/-- A character Unicode allows: up to U+10FFFF, and not one of the surrogates U+D800 to U+DFFF. -/
def Scalar (c : UInt32) : Prop := c < 0xD800 ∨ (0xDFFF < c ∧ c ≤ 0x10FFFF)

/-- UTF-8 as the standard's table gives it. Up to U+007F a character is itself. After that the first byte
says how many bytes there are (110, 1110 or 11110 on top) and holds the character's top bits, and every
later byte is 10 on top of the next six bits. -/
def encoding (c : UInt32) : List UInt8 :=
  if c < 0x80 then [c.toUInt8]
  else if c < 0x800 then [(0xC0 + c / 0x40).toUInt8, (0x80 + c % 0x40).toUInt8]
  else if c < 0x10000 then
    [(0xE0 + c / 0x1000).toUInt8, (0x80 + c / 0x40 % 0x40).toUInt8, (0x80 + c % 0x40).toUInt8]
  else
    [(0xF0 + c / 0x40000).toUInt8, (0x80 + c / 0x1000 % 0x40).toUInt8, (0x80 + c / 0x40 % 0x40).toUInt8,
      (0x80 + c % 0x40).toUInt8]

/-! ## Writing -/

/-- The bytes `write` packs into a word: how many is above bit 32, and they are below it, first lowest. -/
def unpack (w : UInt64) : List UInt8 :=
  if w >>> 32 = 1 then [w.toUInt8]
  else if w >>> 32 = 2 then [w.toUInt8, (w >>> 8).toUInt8]
  else if w >>> 32 = 3 then [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8]
  else [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

theorem unpack_one (w : UInt64) (h : w >>> 32 = 1) : unpack w = [w.toUInt8] := by simp [unpack, h]

theorem unpack_two (w : UInt64) (h : w >>> 32 = 2) : unpack w = [w.toUInt8, (w >>> 8).toUInt8] := by
  simp [unpack, h]

theorem unpack_three (w : UInt64) (h : w >>> 32 = 3) :
    unpack w = [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8] := by
  simp [unpack, h]

theorem unpack_four (w : UInt64) (h : w >>> 32 = 4) :
    unpack w = [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8] := by
  simp [unpack, h]

/-- `write` gives the standard's bytes, for every character up to U+10FFFF. -/
theorem write_encoding (c : UInt32) (h : c ≤ 0x10FFFF) : unpack (write c) = encoding c := by
  simp only [write, encoding]
  split
  · refine (unpack_one _ ?_).trans ?_
    · bv_decide
    · simp only [List.cons.injEq, and_true]; bv_decide
  · split
    · refine (unpack_two _ ?_).trans ?_
      · bv_decide
      · simp only [List.cons.injEq, and_true]; bv_decide
    · split
      · refine (unpack_three _ ?_).trans ?_
        · bv_decide
        · simp only [List.cons.injEq, and_true]; bv_decide
      · refine (unpack_four _ ?_).trans ?_
        · bv_decide
        · simp only [List.cons.injEq, and_true]; bv_decide

/-! ## Reading

`strict` and `read` ask how many bytes are really there by comparing a count. What follows is about the
bytes, so each such comparison is first replaced by its answer. -/

/-- `strict`, with "more than one, two, three bytes are there" already answered. -/
def strictOn (b0 b1 b2 b3 : UInt8) (a1 a2 a3 : Bool) : UInt8 :=
  if b0 < 0x80 then 1
  else if b0 &&& 0xE0 == 0xC0 then
    let value := ((b0.toUInt32 &&& 0x1F) <<< 6) ||| six b1
    if a1 && continues b1 && value ≥ 0x80 then 2 else 0
  else if b0 &&& 0xF0 == 0xE0 then
    let value := ((b0.toUInt32 &&& 0x0F) <<< 12) ||| (six b1 <<< 6) ||| six b2
    if a2 && continues b1 && continues b2 && value ≥ 0x800 && !(value ≥ 0xD800 && value ≤ 0xDFFF)
    then 3 else 0
  else if b0 &&& 0xF8 == 0xF0 then
    let value := ((b0.toUInt32 &&& 0x07) <<< 18) ||| (six b1 <<< 12) ||| (six b2 <<< 6) ||| six b3
    if a3 && continues b1 && continues b2 && continues b3 && value ≥ 0x10000 && value ≤ 0x10FFFF
    then 4 else 0
  else 0

theorem strict_eq (b0 b1 b2 b3 : UInt8) (available : USize) :
    strict b0 b1 b2 b3 available =
      strictOn b0 b1 b2 b3 (decide (available > 1)) (decide (available > 2)) (decide (available > 3)) := rfl

/-- `read`, with the same three questions answered. -/
def readOn (b0 b1 b2 b3 : UInt8) (a1 a2 a3 : Bool) : UInt64 :=
  let found (c : UInt32) : UInt64 := c.toUInt64 ||| 0x100000000
  let two := ((b0.toUInt32 &&& 0x1F) <<< 6) ||| six b1
  let three := ((b0.toUInt32 &&& 0x0F) <<< 12) ||| (six b1 <<< 6) ||| six b2
  let four := ((b0.toUInt32 &&& 0x07) <<< 18) ||| (six b1 <<< 12) ||| (six b2 <<< 6) ||| six b3
  if b0 &&& 0x80 == 0 then found b0.toUInt32
  else if b0 &&& 0xE0 == 0xC0 && a1 && two ≥ 0x80 then found two
  else if b0 &&& 0xF0 == 0xE0 && a2 && three ≥ 0x800 && (three < 0xD800 || three > 0xDFFF) then found three
  else if b0 &&& 0xF8 == 0xF0 && a3 && four ≥ 0x10000 && four ≤ 0x10FFFF then found four
  else 0

theorem read_eq (b0 b1 b2 b3 : UInt8) (available : USize) :
    read b0 b1 b2 b3 available =
      readOn b0 b1 b2 b3 (decide (available > 1)) (decide (available > 2)) (decide (available > 3)) := rfl

/-! ### One byte -/

/-- `strict` says one byte exactly when that byte is the whole encoding of a character. -/
theorem strict_one (b0 b1 b2 b3 : UInt8) (available : USize) :
    strict b0 b1 b2 b3 available = 1 ↔ ∃ c, Scalar c ∧ encoding c = [b0] := by
  rw [strict_eq]
  generalize decide (available > 1) = a1
  generalize decide (available > 2) = a2
  generalize decide (available > 3) = a3
  constructor
  · intro h
    have low : b0.toUInt32 < 0x80 ∧ b0.toUInt32.toUInt8 = b0 := by
      simp only [strictOn, six, continues] at h; bv_decide
    exact ⟨b0.toUInt32, Or.inl (by bv_decide), by simp [encoding, low.1, low.2]⟩
  · rintro ⟨c, -, h⟩
    unfold encoding at h
    split at h
    · rename_i h1
      simp only [List.cons.injEq, and_true] at h
      subst h
      simp only [strictOn, six, continues]
      bv_decide
    · split at h
      · simp at h
      · split at h <;> simp at h

/-! ### Two bytes -/

/-- `strict` says two bytes exactly when both are there and they are the encoding of a character. -/
theorem strict_two (b0 b1 b2 b3 : UInt8) (available : USize) :
    strict b0 b1 b2 b3 available = 2 ↔ available > 1 ∧ ∃ c, Scalar c ∧ encoding c = [b0, b1] := by
  rw [strict_eq]
  have there : available > 1 ↔ decide (available > 1) = true := decide_eq_true_iff.symm
  generalize decide (available > 1) = a1 at there ⊢
  generalize decide (available > 2) = a2
  generalize decide (available > 3) = a3
  rw [there]
  constructor
  · intro h
    generalize hc : ((b0.toUInt32 &&& 0x1F) <<< 6) ||| (b1.toUInt32 &&& 0x3F) = c
    have facts : a1 = true ∧ ¬ c < 0x80 ∧ c < 0x800 ∧ c < 0xD800 ∧
        (0xC0 + c / 0x40).toUInt8 = b0 ∧ (0x80 + c % 0x40).toUInt8 = b1 := by
      subst hc; simp only [strictOn, six, continues] at h; bv_decide
    obtain ⟨f1, f2, f3, f4, f5, f6⟩ := facts
    exact ⟨f1, c, Or.inl f4, by simp [encoding, f2, f3, f5, f6]⟩
  · rintro ⟨ha, c, -, h⟩
    unfold encoding at h
    split at h
    · simp at h
    · split at h
      · rename_i h1 h2
        simp only [List.cons.injEq, and_true] at h
        obtain ⟨e0, e1⟩ := h
        subst e0 e1
        simp only [strictOn, six, continues]
        bv_decide
      · split at h <;> simp at h

/-! ### Three bytes -/

/-- `strict` says three bytes exactly when all three are there and they are the encoding of a character:
so never for a surrogate, which the table would otherwise give three bytes. -/
theorem strict_three (b0 b1 b2 b3 : UInt8) (available : USize) :
    strict b0 b1 b2 b3 available = 3 ↔ available > 2 ∧ ∃ c, Scalar c ∧ encoding c = [b0, b1, b2] := by
  rw [strict_eq]
  have there : available > 2 ↔ decide (available > 2) = true := decide_eq_true_iff.symm
  generalize decide (available > 1) = a1
  generalize decide (available > 2) = a2 at there ⊢
  generalize decide (available > 3) = a3
  rw [there]
  constructor
  · intro h
    generalize hc : ((b0.toUInt32 &&& 0x0F) <<< 12) ||| ((b1.toUInt32 &&& 0x3F) <<< 6) ||| (b2.toUInt32 &&& 0x3F) = c
    have facts : a2 = true ∧ ¬ c < 0x80 ∧ ¬ c < 0x800 ∧ c < 0x10000 ∧ (c < 0xD800 ∨ (0xDFFF < c ∧ c ≤ 0x10FFFF)) ∧
        (0xE0 + c / 0x1000).toUInt8 = b0 ∧ (0x80 + c / 0x40 % 0x40).toUInt8 = b1 ∧
        (0x80 + c % 0x40).toUInt8 = b2 := by
      subst hc; simp only [strictOn, six, continues] at h; bv_decide
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := facts
    exact ⟨f1, c, f5, by simp [encoding, f2, f3, f4, f6, f7, f8]⟩
  · rintro ⟨ha, c, hc, h⟩
    unfold Scalar at hc
    unfold encoding at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rename_i h1 h2 h3
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨e0, e1, e2⟩ := h
          subst e0 e1 e2
          simp only [strictOn, six, continues]
          bv_decide
        · simp at h

/-! ### Four bytes -/

/-- `strict` says four bytes exactly when all four are there and they are the encoding of a character: so
never for anything above U+10FFFF. -/
theorem strict_four (b0 b1 b2 b3 : UInt8) (available : USize) :
    strict b0 b1 b2 b3 available = 4 ↔ available > 3 ∧ ∃ c, Scalar c ∧ encoding c = [b0, b1, b2, b3] := by
  rw [strict_eq]
  have there : available > 3 ↔ decide (available > 3) = true := decide_eq_true_iff.symm
  generalize decide (available > 1) = a1
  generalize decide (available > 2) = a2
  generalize decide (available > 3) = a3 at there ⊢
  rw [there]
  constructor
  · intro h
    generalize hc : ((b0.toUInt32 &&& 0x07) <<< 18) ||| ((b1.toUInt32 &&& 0x3F) <<< 12) |||
      ((b2.toUInt32 &&& 0x3F) <<< 6) ||| (b3.toUInt32 &&& 0x3F) = c
    have facts : a3 = true ∧ ¬ c < 0x80 ∧ ¬ c < 0x800 ∧ ¬ c < 0x10000 ∧ 0xDFFF < c ∧ c ≤ 0x10FFFF ∧
        (0xF0 + c / 0x40000).toUInt8 = b0 ∧ (0x80 + c / 0x1000 % 0x40).toUInt8 = b1 ∧
        (0x80 + c / 0x40 % 0x40).toUInt8 = b2 ∧ (0x80 + c % 0x40).toUInt8 = b3 := by
      subst hc; simp only [strictOn, six, continues] at h; bv_decide
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩ := facts
    exact ⟨f1, c, Or.inr ⟨f5, f6⟩, by simp [encoding, f2, f3, f4, f7, f8, f9, f10]⟩
  · rintro ⟨ha, c, hc, h⟩
    unfold Scalar at hc
    unfold encoding at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i h1 h2 h3
          simp only [List.cons.injEq, and_true] at h
          obtain ⟨e0, e1, e2, e3⟩ := h
          subst e0 e1 e2 e3
          simp only [strictOn, six, continues]
          bv_decide

/-- `strict` answers nothing but zero to four. -/
theorem strict_le (b0 b1 b2 b3 : UInt8) (available : USize) : strict b0 b1 b2 b3 available ≤ 4 := by
  rw [strict_eq]
  generalize decide (available > 1) = a1
  generalize decide (available > 2) = a2
  generalize decide (available > 3) = a3
  simp only [strictOn, six, continues]
  bv_decide

/-! ### What is read, and how far to step -/

/-- Where `strict` finds a well-formed character, `read` returns the character those bytes encode, with bit
32 set, and `claims` steps over exactly its bytes. `c` is the character put back together from as many bytes
as `strict` counted. -/
theorem read_strict (b0 b1 b2 b3 : UInt8) (available : USize) (most : UInt8) :
    (strict b0 b1 b2 b3 available = 1 → read b0 b1 b2 b3 available = b0.toUInt64 ||| 0x100000000) ∧
    (strict b0 b1 b2 b3 available = 2 → read b0 b1 b2 b3 available =
      (((b0.toUInt32 &&& 0x1F) <<< 6) ||| (b1.toUInt32 &&& 0x3F)).toUInt64 ||| 0x100000000) ∧
    (strict b0 b1 b2 b3 available = 3 → read b0 b1 b2 b3 available =
      (((b0.toUInt32 &&& 0x0F) <<< 12) ||| ((b1.toUInt32 &&& 0x3F) <<< 6) |||
        (b2.toUInt32 &&& 0x3F)).toUInt64 ||| 0x100000000) ∧
    (strict b0 b1 b2 b3 available = 4 → read b0 b1 b2 b3 available =
      (((b0.toUInt32 &&& 0x07) <<< 18) ||| ((b1.toUInt32 &&& 0x3F) <<< 12) ||| ((b2.toUInt32 &&& 0x3F) <<< 6) |||
        (b3.toUInt32 &&& 0x3F)).toUInt64 ||| 0x100000000) ∧
    (strict b0 b1 b2 b3 available ≠ 0 → claims b0 most = strict b0 b1 b2 b3 available) := by
  rw [strict_eq, read_eq]
  generalize decide (available > 1) = a1
  generalize decide (available > 2) = a2
  generalize decide (available > 3) = a3
  simp only [strictOn, readOn, claims, six, continues]
  bv_decide

end Runtime.Utf8
