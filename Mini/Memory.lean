import Mini.Run

/-! # Memory, for proofs

What reading gives after writing: the facts about `readBytes` and `writeBytes` that every proof about a
program that touches memory stands on. Addresses are words and wrap, so "a different address" is a fact
about arithmetic modulo 2^64; a run of up to eight bytes never meets itself. -/

namespace Mini

/-- Writing a run of bytes leaves every address outside the run as it was. -/
theorem writeBytes_other (memory : UInt64 → Option UInt8) (start word : UInt64) (count : Nat) (x : UInt64)
    (outside : ∀ k, k < count → start + UInt64.ofNat k ≠ x) :
    writeBytes memory start word count x = memory x := by
  induction count generalizing memory start word with
  | zero => rfl
  | succ count ih =>
    rw [writeBytes, ih]
    · have first : start ≠ x := by simpa using outside 0 (by omega)
      simp [put, Ne.symm first]
    · intro k hk
      have := outside (k + 1) (by omega)
      rwa [show start + UInt64.ofNat (k + 1) = start + 1 + UInt64.ofNat k from by
        rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat k)]; rfl] at this

/-- A step of one and up to seven more never comes back to where it started. -/
theorem step_ne (a : UInt64) (k : Nat) (hk : k < 8) : a + 1 + UInt64.ofNat k ≠ a := by
  intro h
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl] at this
  have := a.toNat_lt
  omega

/-- Reading back what was just written, up to eight bytes of it: the low bytes of the word. -/
theorem readBytes_writeBytes (memory : UInt64 → Option UInt8) (a word : UInt64) (count : Nat) (h : count ≤ 8) :
    ∃ r, readBytes (writeBytes memory a word count) a count = .ok r ∧ r.toNat = word.toNat % 2 ^ (8 * count) := by
  induction count generalizing memory a word with
  | zero => exact ⟨0, rfl, (Nat.mod_one _).symm⟩
  | succ count ih =>
    obtain ⟨rest, hrest, hvalue⟩ := ih (put memory a (some word.toUInt8)) (a + 1) (word >>> 8) (by omega)
    have first : writeBytes (put memory a (some word.toUInt8)) (a + 1) (word >>> 8) count a = some word.toUInt8 := by
      rw [writeBytes_other _ _ _ _ _ (fun k hk => step_ne a k (by omega))]
      simp [put]
    refine ⟨word.toUInt8.toUInt64 ||| (rest <<< 8), ?_, ?_⟩
    · simp [writeBytes, readBytes, first, hrest]
      rfl
    · have small : rest.toNat < 2 ^ (8 * count) := by rw [hvalue]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      have bound : 2 ^ (8 * count) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) (by omega)
      have shifted : (word >>> 8).toNat = word.toNat / 256 := by
        simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      have low : word.toUInt8.toUInt64.toNat = word.toNat % 256 := by simp
      have high : (rest <<< 8).toNat = rest.toNat * 256 := by
        simp only [UInt64.toNat_shiftLeft, show (8 : UInt64).toNat % 64 = 8 from rfl, Nat.shiftLeft_eq]
        omega
      have e1 : (word.toUInt8.toUInt64 ||| (rest <<< 8)).toNat = rest.toNat * 256 + word.toNat % 256 := by
        rw [UInt64.toNat_or, low, high, Nat.or_comm,
          show rest.toNat * 256 = rest.toNat <<< 8 from by simp [Nat.shiftLeft_eq],
          ← Nat.shiftLeft_add_eq_or_of_lt (show word.toNat % 256 < 2 ^ 8 from Nat.mod_lt _ (by decide))]
      have e2 : 2 ^ (8 * (count + 1)) = 256 * 2 ^ (8 * count) := by
        rw [show 8 * (count + 1) = 8 + 8 * count from by omega, Nat.pow_add]
      rw [e1, e2, Nat.mod_mul, hvalue, shifted]
      omega

/-- Reading back a whole word that was just written. -/
theorem readBytes_writeBytes_word (memory : UInt64 → Option UInt8) (a word : UInt64) :
    readBytes (writeBytes memory a word 8) a 8 = .ok word := by
  obtain ⟨r, hr, hvalue⟩ := readBytes_writeBytes memory a word 8 (Nat.le_refl _)
  have : r = word := UInt64.toNat_inj.mp (by rw [hvalue]; have := word.toNat_lt; omega)
  rw [hr, this]

/-- Reading a run that a write did not touch gives what it gave before. -/
theorem readBytes_writeBytes_other (memory : UInt64 → Option UInt8) (start word : UInt64) (count : Nat)
    (x : UInt64) (n : Nat)
    (apart : ∀ i, i < n → ∀ k, k < count → start + UInt64.ofNat k ≠ x + UInt64.ofNat i) :
    readBytes (writeBytes memory start word count) x n = readBytes memory x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have here : writeBytes memory start word count x = memory x :=
      writeBytes_other _ _ _ _ _ (fun k hk => by simpa using apart 0 (by omega) k hk)
    have further : readBytes (writeBytes memory start word count) (x + 1) n = readBytes memory (x + 1) n :=
      ih (x + 1) (fun i hi k hk => by
        have := apart (i + 1) (by omega) k hk
        rwa [show x + UInt64.ofNat (i + 1) = x + 1 + UInt64.ofNat i from by
          rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat i)]; rfl] at this)
    simp only [readBytes, here, further]

/-- Two words sixteen bytes or less apart, but not at the same place, do not share a byte: the word at
`a + d` and the word at `a`, for `d` from 8 to 2^64 - 8. -/
theorem words_apart (a d : UInt64) (low : 8 ≤ d.toNat) (high : d.toNat ≤ 18446744073709551608)
    (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8) : a + UInt64.ofNat k ≠ a + d + UInt64.ofNat i := by
  intro h
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  have := a.toNat_lt
  omega

end Mini
