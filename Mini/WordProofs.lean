import Std.Tactic.BVDecide

/-! # The arithmetic tricks, proved

The few lines of word arithmetic that stand in for a branch or a compiler built-in, proved for every value.
The three about masks are proved with `bv_decide`, which hands the question to a SAT solver and checks its
answer with compiled code, recorded as an axiom of its own (`#print axioms` shows one per proof). They trust
the compiler that ran that check, beyond Lean's three standard axioms. The two about overflow use the three
standard axioms only, as the allocator's proofs do. -/

namespace Mini.WordProofs

/-- The index mask of `Stmt.inBounds` (Linux's `array_index_nospec`): the index itself when it is below the
size, and zero otherwise, for indices and sizes up to 2^63. -/
theorem inBounds_mask (i n : UInt64) (hi : i < 0x8000000000000000) (hn : n ≤ 0x8000000000000000) :
    i &&& (((i ||| (n - 1 - i)) >>> 63) - 1) = if i < n then i else 0 := by
  split <;> bv_decide

/-- `silo_secret_select`: `x` for a bit of 1, `y` for 0. -/
theorem select_mask (bit x y : UInt64) :
    y ^^^ ((x ^^^ y) &&& (0 - (bit &&& 1))) = if bit &&& 1 = 1 then x else y := by
  split <;> bv_decide

/-- The end of `silo_secret_equal`: the differences gathered are at most 255, and the answer is 1 exactly
when there were none. -/
theorem equal_end (d : UInt64) (h : d < 256) : (d - 1) >>> 63 = if d = 0 then 1 else 0 := by
  split <;> bv_decide

/-- `add_checked` stops exactly when the sum does not fit in a word. -/
theorem add_wraps (a b : UInt64) : a + b < a ↔ 2 ^ 64 ≤ a.toNat + b.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  have := a.toNat_lt_size
  have := b.toNat_lt_size
  simp only [UInt64.size] at *
  omega

/-- `mul_checked` stops exactly when the product does not fit in a word. -/
theorem mul_wraps (a b : UInt64) (ha : a ≠ 0) : (a * b) / a ≠ b ↔ 2 ^ 64 ≤ a.toNat * b.toNat := by
  have hapos : 0 < a.toNat := by
    have : a.toNat ≠ 0 := fun h => ha (UInt64.toNat_inj.mp (by simpa using h))
    omega
  rw [Ne, ← UInt64.toNat_inj, UInt64.toNat_div, UInt64.toNat_mul]
  have hb := b.toNat_lt_size
  simp only [UInt64.size] at *
  constructor
  · intro h
    apply Classical.byContradiction
    intro hlt
    exact h (by rw [Nat.mod_eq_of_lt (by omega), Nat.mul_div_cancel_left _ hapos])
  · intro h heq
    -- What is left after wrapping is under 2^64, and a times its quotient by a is no more than it.
    have hm : a.toNat * b.toNat % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
    have hq := Nat.mul_div_le (a.toNat * b.toNat % 2 ^ 64) a.toNat
    rw [heq] at hq
    omega

end Mini.WordProofs
