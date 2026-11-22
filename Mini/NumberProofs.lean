import Mini.Run
import Mini.Memory
import Mini.Number
import Mini.AllocProofs
import Runtime.BigProofs

/-! # What is proved about numbers in memory

Statements about the program in `Mini/Number.lean` as `Mini/Run.lean` defines its meaning. The arithmetic
itself is `Runtime/Big.lean`, proved in `Runtime/BigProofs.lean` to return the limbs of the right number;
this is about the two ends of a call: that the limbs handed to it are those of the number that came in, and
that what goes back to compiled Lean is the number in the limbs it returned. Nothing here runs; no image
imports it.

What the program calls outside itself is an assumption in each statement. For one function at a time it is
that `lean_alloc_object` returned some address, and for `nat_from` and `int_from` that `lean_dec` returned.
For a number that fits in a tagged word nothing more is assumed. For one that is an object, two things are
assumed of the room `lean_alloc_object` hands out, since the program reads an object or an array while it
writes into that room: the room shares no byte with what is being read, and making the room left what is
being read as it was. Nothing is assumed of what the room held.

For an operation as a whole the assumptions are gathered into definitions, each a hypothesis of the
statement that uses it: `Allocator`, what `lean_alloc_object` and `lean_dec` do; `Computes` and `Compares`,
and for integers `ComputesSigned` and `ComparesSigned`, what a call into the compiled arithmetic does. Those
statements are of an operation that returns. Where the allocator does not return, the operation is shown
not to return either; nothing else is said of it then.

First numbers that fit in a tagged word, natural numbers and then integers; then numbers that are objects;
then operations as wholes, on natural numbers and then on integers. -/

namespace Mini.Number

theorem find_arrayNew : program.functions.find? (fun f => f.name == "array_new") = some arrayNew := rfl
theorem find_limbsOfWord : program.functions.find? (fun f => f.name == "limbs_of_word") = some limbsOfWord := rfl

/-- The header of an array with one reference. -/
def arrayHeader : UInt64 := UInt64.ofNat (1 + arrayKind * 2 ^ 56)

/-- `array_new` asks for room for the header, the size, the capacity and the elements, and writes the first
three. -/
theorem arrayNew_runs (outside : Outside) (fuel : Nat) (count array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [24 + count * 8] s = .ok (array, s')) :
    program.call outside (fuel + 10) "array_new" [count] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (writeBytes (writeBytes s'.memory array arrayHeader 8) (array + 8) count 8)
            (array + 16) count 8 }) := by
  simp [Program.call, find_arrayNew, arrayNew, runAll, Stmt.run, Expr.run, Op.run, bind, put, header, alloc]
  rfl

/-- Memory with the first three words of an array written: its header, its size and its capacity. -/
def headed (memory : UInt64 → Option UInt8) (array count : UInt64) : UInt64 → Option UInt8 :=
  writeBytes (writeBytes (writeBytes memory array arrayHeader 8) (array + 8) count 8) (array + 16) count 8

/-- A limb as an element of a Lean array: a tagged word. -/
def boxed (limb : UInt64) : UInt64 := (limb <<< 1) ||| 1

theorem limbsOfWord_zero (outside : Outside) (fuel : Nat) (array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [24] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [0] s =
      .ok (.gave array, { s' with memory := headed s'.memory array 0 }) := by
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc]
  rfl

theorem limbsOfWord_one (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (hz : value ≠ 0) (hs : value ≤ 4294967295)
    (alloc : outside "lean_alloc_object" [32] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [value] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (headed s'.memory array 1) (array + 24) (boxed (value &&& 4294967295)) 8 }) := by
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc, hz, hs]
  rfl

theorem limbsOfWord_two (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (hl : (4294967295 : UInt64) < value)
    (alloc : outside "lean_alloc_object" [40] s = .ok (array, s')) :
    program.call outside (fuel + 20) "limbs_of_word" [value] s =
      .ok (.gave array,
        { s' with
          memory := writeBytes (writeBytes (headed s'.memory array 2) (array + 24) (boxed (value &&& 4294967295)) 8)
            (array + 32) (boxed (value >>> 32)) 8 }) := by
  have hz : value ≠ 0 := by intro h; subst h; exact absurd hl (by decide)
  have hn : ¬ value ≤ 4294967295 := by simpa [UInt64.not_le] using hl
  simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc, hz, hn]
  rfl

/-! ## Words apart -/

/-- A word written eight bytes or more from another, either way round, leaves the other as it was. -/
theorem read_apart (memory : UInt64 → Option UInt8) (p q word : UInt64)
    (low : 8 ≤ (q - p).toNat) (high : (q - p).toNat ≤ 18446744073709551608) :
    readBytes (writeBytes memory p word 8) q 8 = readBytes memory q 8 := by
  have back : p + (q - p) = q := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_sub]
    have := p.toNat_lt
    have := q.toNat_lt
    omega
  exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => by
    have := words_apart p (q - p) low high i hi k hk
    rwa [back] at this)

/-- The same for two places counted from one address. -/
theorem read_off (memory : UInt64 → Option UInt8) (a word : UInt64) (x y : Nat)
    (hx : x < 9223372036854775808) (hy : y < 9223372036854775808) (apart : x + 8 ≤ y ∨ y + 8 ≤ x) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word 8) (a + UInt64.ofNat y) 8
      = readBytes memory (a + UInt64.ofNat y) 8 := by
  have d : (a + UInt64.ofNat y - (a + UInt64.ofNat x)).toNat
      = (y + 18446744073709551616 - x) % 18446744073709551616 := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

/-- A write inside the first `n` bytes from an address leaves everything outside them as it was. -/
theorem write_inside (memory : UInt64 → Option UInt8) (a word p : UInt64) (off n : Nat) (h : off + 8 ≤ n)
    (outside : ∀ k, k < n → a + UInt64.ofNat k ≠ p) :
    writeBytes memory (a + UInt64.ofNat off) word 8 p = memory p := by
  refine writeBytes_other _ _ _ _ _ (fun k hk => ?_)
  have := outside (off + k) (by omega)
  rwa [UInt64.ofNat_add, ← UInt64.add_assoc] at this

/-! ## An array of limbs in memory -/

/-- A Lean array of limbs at an address, as much of it as this program makes and reads: its header, its
size, and each limb as a tagged word. -/
def ArrayOf (memory : UInt64 → Option UInt8) (array : UInt64) (limbs : Runtime.Big.Limbs) : Prop :=
  readBytes memory array 8 = .ok arrayHeader ∧
  readBytes memory (array + 8) 8 = .ok (UInt64.ofNat limbs.size) ∧
  ∀ i, (h : i < limbs.size) →
    readBytes memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64)

/-- The limbs of a number that fits in a word: none for zero, one below 2^32, otherwise two. -/
def wordLimbs (value : UInt64) : Runtime.Big.Limbs :=
  if value = 0 then #[] else if value ≤ 4294967295 then #[value.toUInt32]
  else #[value.toUInt32, (value >>> 32).toUInt32]

/-- They are the limbs of that number. -/
theorem wordLimbs_value (value : UInt64) : Runtime.Big.value (wordLimbs value) = value.toNat := by
  have lt := value.toNat_lt
  unfold wordLimbs
  split
  · rename_i h; subst h; rfl
  · split
    · rename_i h1 h2
      have small : value.toNat ≤ 4294967295 := by simpa [UInt64.le_iff_toNat_le] using h2
      simp [Runtime.Big.value, Runtime.Big.valueList]
      omega
    · rename_i h1 h2
      simp [Runtime.Big.value, Runtime.Big.valueList, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      omega

/-- And they have no zero limb on top, which is how the arithmetic expects a number. -/
theorem wordLimbs_trimmed (value : UInt64) : Runtime.Big.Trimmed (wordLimbs value) := by
  have lt := value.toNat_lt
  unfold wordLimbs
  split
  · exact Or.inl rfl
  · split
    · rename_i h1 h2
      have nz : value.toNat ≠ 0 := fun z => h1 (UInt64.toNat_inj.mp (by rw [z]; rfl))
      have small : value.toNat ≤ 4294967295 := by simpa [UInt64.le_iff_toNat_le] using h2
      refine Or.inr ?_
      simp [Runtime.Big.digit]
      omega
    · rename_i h1 h2
      have large : 4294967295 < value.toNat := by simpa [UInt64.le_iff_toNat_le] using h2
      refine Or.inr ?_
      simp [Runtime.Big.digit, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
      omega

/-! ## What `limbs_of_word` leaves in memory -/

theorem read_base (memory : UInt64 → Option UInt8) (a word : UInt64) (x : Nat)
    (hx : 8 ≤ x) (hx' : x < 9223372036854775808) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word 8) a 8 = readBytes memory a 8 := by
  have d : (a - (a + UInt64.ofNat x)).toNat = 18446744073709551616 - x := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

theorem read_from_base (memory : UInt64 → Option UInt8) (a word : UInt64) (y : Nat)
    (hy : 8 ≤ y) (hy' : y < 9223372036854775808) :
    readBytes (writeBytes memory a word 8) (a + UInt64.ofNat y) 8 = readBytes memory (a + UInt64.ofNat y) 8 := by
  have d : (a + UInt64.ofNat y - a).toNat = y := by
    simp only [UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_ofNat']
    have := a.toNat_lt
    omega
  exact read_apart _ _ _ _ (by rw [d]; omega) (by rw [d]; omega)

theorem headed_header (memory : UInt64 → Option UInt8) (a count : UInt64) :
    readBytes (headed memory a count) a 8 = .ok arrayHeader := by
  exact (read_base _ a _ 16 (by omega) (by omega)).trans
    ((read_base _ a _ 8 (by omega) (by omega)).trans (readBytes_writeBytes_word _ _ _))

theorem headed_size (memory : UInt64 → Option UInt8) (a count : UInt64) :
    readBytes (headed memory a count) (a + 8) 8 = .ok count := by
  exact (read_off _ a _ 16 8 (by omega) (by omega) (by omega)).trans (readBytes_writeBytes_word _ _ _)

/-- The header, size and capacity are the first 24 bytes: writing them leaves the elements as they were. -/
theorem headed_element (memory : UInt64 → Option UInt8) (a count : UInt64) (y : Nat)
    (hy : 24 ≤ y) (hy' : y < 9223372036854775808) :
    readBytes (headed memory a count) (a + UInt64.ofNat y) 8 = readBytes memory (a + UInt64.ofNat y) 8 := by
  exact (read_off _ a _ 16 y (by omega) hy' (by omega)).trans
    ((read_off _ a _ 8 y (by omega) hy' (by omega)).trans (read_from_base _ a _ y (by omega) hy'))

theorem headed_outside (memory : UInt64 → Option UInt8) (a count p : UInt64) (n : Nat) (hn : 24 ≤ n)
    (outside : ∀ k, k < n → a + UInt64.ofNat k ≠ p) : headed memory a count p = memory p := by
  have first : writeBytes memory a arrayHeader 8 p = memory p := by
    simpa using write_inside memory a arrayHeader p 0 n (by omega) outside
  exact (write_inside _ a _ p 16 n (by omega) outside).trans
    ((write_inside _ a _ p 8 n (by omega) outside).trans first)

theorem low_limb (value : UInt64) : value &&& 4294967295 = value.toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  simp

theorem high_limb (value : UInt64) : value >>> 32 = (value >>> 32).toUInt32.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have := value.toNat_lt
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  omega

/-- `limbs_of_word` hands the arithmetic the right limbs: given room for them, it leaves in memory an array
holding the limbs of the word (`wordLimbs`, whose number is the word and which has no zero limb on top),
does nothing C leaves open, and changes nothing outside the room it was given. -/
theorem limbsOfWord_array (outside : Outside) (fuel : Nat) (value array : UInt64) (s s' : State)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs value).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 20) "limbs_of_word" [value] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs value)
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs value).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  by_cases hz : value = 0
  · subst hz
    have w : wordLimbs 0 = #[] := rfl
    rw [w] at alloc ⊢
    exact ⟨_, limbsOfWord_zero outside fuel array s s' alloc,
      ⟨headed_header _ _ _, headed_size _ _ _, fun i h => absurd h (by simp)⟩,
      fun p out => headed_outside _ _ _ _ 24 (by omega) out⟩
  · by_cases hs : value ≤ 4294967295
    · have w : wordLimbs value = #[value.toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc ⊢
      refine ⟨_, limbsOfWord_one outside fuel value array s s' hz hs alloc, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (read_base _ array _ 24 (by omega) (by omega)).trans (headed_header _ _ _)
      · exact (read_off _ array _ 24 8 (by omega) (by omega) (by omega)).trans (headed_size _ _ _)
      · intro i h
        have i0 : i = 0 := by simp at h; omega
        subst i0
        show readBytes _ (array + 24) 8 = _
        rw [readBytes_writeBytes_word, low_limb]
        rfl
      · intro p out
        exact (write_inside _ array _ p 24 32 (by omega) out).trans (headed_outside _ _ _ _ 32 (by omega) out)
    · have hl : (4294967295 : UInt64) < value := by simpa [UInt64.not_le] using hs
      have w : wordLimbs value = #[value.toUInt32, (value >>> 32).toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc ⊢
      refine ⟨_, limbsOfWord_two outside fuel value array s s' hl alloc, ⟨?_, ?_, ?_⟩, ?_⟩
      · exact (read_base _ array _ 32 (by omega) (by omega)).trans
          ((read_base _ array _ 24 (by omega) (by omega)).trans (headed_header _ _ _))
      · exact (read_off _ array _ 32 8 (by omega) (by omega) (by omega)).trans
          ((read_off _ array _ 24 8 (by omega) (by omega) (by omega)).trans (headed_size _ _ _))
      · intro i h
        have i01 : i = 0 ∨ i = 1 := by simp at h; omega
        rcases i01 with rfl | rfl
        · show readBytes _ (array + 24) 8 = _
          refine (read_off _ array _ 32 24 (by omega) (by omega) (by omega)).trans ?_
          refine (readBytes_writeBytes_word _ _ _).trans ?_
          rw [low_limb]
          rfl
        · show readBytes _ (array + 32) 8 = _
          exact (readBytes_writeBytes_word _ _ _).trans
            (congrArg (fun x => Except.ok (boxed x)) (high_limb value))
      · intro p out
        exact (write_inside _ array _ p 32 40 (by omega) out).trans
          ((write_inside _ array _ p 24 40 (by omega) out).trans (headed_outside _ _ _ _ 40 (by omega) out))

/-! ## A natural number that arrives as a tagged word -/

theorem find_natLimbs : program.functions.find? (fun f => f.name == "nat_limbs") = some natLimbs := rfl

/-- What calling a function by name says about running its body. -/
theorem runAll_of_call (p : Program) (outside : Outside) (fuel : Nat) (function : String) (f : Function)
    (arguments : List UInt64) (s after : State) (ending : Ending)
    (found : p.functions.find? (fun f => f.name == function) = some f)
    (call : p.call outside fuel function arguments s = .ok (ending, after)) :
    ∃ locals, runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments)
      = .ok (ending, after, locals) := by
  unfold Program.call at call
  rw [found] at call
  dsimp only at call
  cases run : runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments) with
  | error e =>
    rw [run] at call
    cases call
  | ok r =>
    obtain ⟨e, st, l⟩ := r
    rw [run] at call
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at call
    injection call with same
    injection same with e1 e2
    exact ⟨l, by rw [e1, e2]⟩

/-- A natural number below 2^63 arrives as a tagged word: the number moved up one bit, with the lowest bit
set. `nat_limbs` hands the arithmetic the limbs of that number. -/
theorem natLimbs_word (outside : Outside) (fuel : Nat) (o array : UInt64) (s s' : State) (tagged : o &&& 1 ≠ 0)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (o >>> 1)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 24) "nat_limbs" [o] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (o >>> 1))
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (o >>> 1)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  obtain ⟨memory, run, holds, frame⟩ := limbsOfWord_array outside fuel (o >>> 1) array s s' alloc
  obtain ⟨l, hl⟩ := runAll_of_call program outside (fuel + 20) "limbs_of_word" limbsOfWord [o >>> 1] s _ _
    find_limbsOfWord run
  refine ⟨memory, ?_, holds, frame⟩
  simp [Program.call, find_natLimbs, find_limbsOfWord, natLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
    isWord, unbox, Expr.ne, Expr.and, Expr.shr, tagged, hl]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]

/-! ## Reading an answer: the zero limbs on top -/

theorem find_trimmed : program.functions.find? (fun f => f.name == "trimmed") = some trimmed := rfl

/-- How many of the first `n` limbs are left when the zero ones on top are dropped: what `trimmed` counts. -/
def trimCount (limbs : Runtime.Big.Limbs) : Nat → Nat
  | 0 => 0
  | n + 1 => if limbs.getD n 0 = 0 then trimCount limbs n else n + 1

theorem trimCount_le (limbs : Runtime.Big.Limbs) (n : Nat) : trimCount limbs n ≤ n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => unfold trimCount; split <;> omega

/-- A tagged word with its tag taken off is the limb it held. -/
theorem unbox_boxed (limb : UInt32) : boxed limb.toUInt64 >>> 1 = limb.toUInt64 := by
  apply UInt64.toNat_inj.mp
  have lt := limb.toNat_lt
  have e : (limb.toNat <<< 1 ||| 1) = limb.toNat <<< 1 + 1 :=
    (Nat.shiftLeft_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) limb.toNat).symm
  simp only [boxed, UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64,
    show (1 : UInt64).toNat = 1 from rfl, show 1 % 64 = 1 from rfl]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), e, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- The loop in `trimmed`, under a name of its own. -/
def trimLoop (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :=
  Stmt.run p outside fuel (.loop (Expr.lt 0 "count")
    [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)]) s locals

/-- The address of the limb below a count that is not zero. -/
theorem below_count (array : UInt64) (n : Nat) :
    array + 24 + (UInt64.ofNat (n + 1) - 1) * 8 = array + UInt64.ofNat (24 + 8 * n) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
    show (24 : UInt64).toNat = 24 from rfl, show (8 : UInt64).toNat = 8 from rfl,
    show (1 : UInt64).toNat = 1 from rfl]
  omega

/-- The loop, from any count: it reads only limbs below the count, changes nothing, and stops at the first
limb from the top that is not zero, giving the count there; or runs out of limbs and goes on with a count
of zero. -/
theorem trim_loop (p : Program) (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64)) :
    ∀ (n : Nat) (locals : Locals) (extra : Nat), n ≤ limbs.size →
      locals "count" = some (UInt64.ofNat n) → locals "array" = some array →
      ∃ after, trimLoop p outside (n + extra + 6) s locals =
          .ok (if trimCount limbs n = 0 then .on else .gave (UInt64.ofNat (trimCount limbs n)), s, after) ∧
        after "count" = some (UInt64.ofNat (trimCount limbs n)) := by
  intro n
  induction n with
  | zero =>
    intro locals extra _ hcount harray
    refine ⟨locals, ?_, by simpa [trimCount] using hcount⟩
    simp [trimLoop, Stmt.run, Expr.run, Op.run, Expr.lt, hcount, trimCount]
    rfl
  | succ n ih =>
    intro locals extra hn hcount harray
    have read := elements n (by omega)
    rw [← below_count] at read
    have value : limbs.getD n 0 = limbs[n]'(by omega) := by simp [Array.getD, show n < limbs.size by omega]
    generalize hc : UInt64.ofNat (n + 1) = c at hcount read
    have cpos : c ≠ 0 := by
      intro z
      have := congrArg UInt64.toNat (hc.trans z)
      simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
      omega
    have cless : c - 1 = UInt64.ofNat n := by
      rw [← hc]
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
      omega
    unfold trimLoop
    rw [show n + 1 + extra + 6 = (n + extra + 6) + 1 from by omega, Mini.Alloc.loop_turn]
    by_cases top : limbs[n]'(by omega) = 0
    · have hz : (limbs[n]'(by omega)).toUInt64 = 0 := by rw [top]; rfl
      obtain ⟨after, hrun, hafter⟩ := ih (put locals "count" (some (c - 1))) extra (by omega)
        (by simp [put, cless]) (by simp [put, harray])
      refine ⟨after, ?_, ?_⟩
      · unfold trimLoop at hrun
        generalize hround : Stmt.run p outside (n + extra + 6) (.loop (Expr.lt 0 "count")
          [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)])
          = round at hrun ⊢
        simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.ne, Expr.shr, limbAt, unbox, hcount, harray, read,
          hz, cpos]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, hcount, hrun, trimCount,
          value, top, show boxed 0 >>> 1 = 0 from by decide]
      · simpa [trimCount, value, top] using hafter
    · have nz : (limbs[n]'(by omega)).toUInt64 ≠ 0 := fun h => top (UInt32.toNat_inj.mp (by
        have := congrArg UInt64.toNat h
        simpa using this))
      refine ⟨locals, ?_, by simpa [trimCount, value, top, hc] using hcount⟩
      generalize hround : Stmt.run p outside (n + extra + 6) (.loop (Expr.lt 0 "count")
        [.branch (Expr.ne (limbAt "array" ("count" - 1)) 0) [.give "count"] [], .set "count" ("count" - 1)])
        = round
      simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.ne, Expr.shr, limbAt, unbox, hcount, harray, read,
        cpos]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, trimCount, value, top, hc, unbox_boxed, nz]

/-- `trimmed` gives the count without the zero limbs on top, and changes nothing. -/
theorem trimmed_runs (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64))
    (n extra : Nat) (hn : n ≤ limbs.size) :
    program.call outside (n + extra + 8) "trimmed" [array, UInt64.ofNat n] s
      = .ok (.gave (UInt64.ofNat (trimCount limbs n)), s) := by
  obtain ⟨after, hrun, hafter⟩ := trim_loop program outside array limbs s small elements n
    (bind (fun _ => none) ["array", "count"] [array, UInt64.ofNat n]) (extra + 1) hn
    (by simp [bind, put]) (by simp [bind, put])
  have step : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n])
      = (do
          match ← trimLoop program outside (n + (extra + 1) + 6) s
              (bind (fun _ => none) ["array", "count"] [array, UInt64.ofNat n]) with
          | (.on, s, locals) => runAll program outside (n + (extra + 1) + 6) [.give "count"] s locals
          | ended => pure ended) := by
    rw [show n + extra + 8 = (n + (extra + 1) + 6) + 1 from by omega]
    rfl
  unfold Program.call
  rw [find_trimmed]
  dsimp only
  rw [step, hrun]
  by_cases z : trimCount limbs n = 0
  · rw [z] at hafter
    simp [z, runAll, Stmt.run, Expr.run, hafter, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · simp [z, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- The number in the limbs is the number in those `trimmed` keeps. -/
theorem value_trimCount (limbs : Runtime.Big.Limbs) (n : Nat) (h : Runtime.Big.tail limbs n = 0) :
    Runtime.Big.value limbs = Runtime.Big.lower limbs (trimCount limbs n) := by
  induction n with
  | zero => rw [Runtime.Big.tail_zero] at h; rw [h]; rfl
  | succ n ih =>
    unfold trimCount
    split
    · rename_i z
      have step := Runtime.Big.tail_step limbs n
      have d : Runtime.Big.digit limbs n = 0 := by simp [Runtime.Big.digit, z]
      rw [h, d, Nat.zero_add] at step
      exact ih (step.trans (Nat.mul_zero _))
    · have split := Runtime.Big.value_split limbs (n + 1)
      rw [h, Nat.mul_zero, Nat.add_zero] at split
      exact split

/-- And the top one of those is not zero. -/
theorem trimCount_top (limbs : Runtime.Big.Limbs) (n m : Nat) (h : trimCount limbs n = m + 1) :
    Runtime.Big.digit limbs m ≠ 0 := by
  induction n with
  | zero => simp [trimCount] at h
  | succ n ih =>
    unfold trimCount at h
    split at h
    · exact ih h
    · rename_i nz
      have e : m = n := by omega
      subst e
      intro z
      exact nz (UInt32.toNat_inj.mp (show (limbs.getD m 0).toNat = (0 : UInt32).toNat from z))

/-! ## Reading an answer that fits in a tagged word -/

theorem find_natResult : program.functions.find? (fun f => f.name == "nat_result") = some natResult := rfl

/-- A number below 2^63 as a tagged word: twice the number, and one. -/
theorem boxed_small (x : UInt64) (h : x.toNat < 9223372036854775808) :
    boxed x = UInt64.ofNat (2 * x.toNat + 1) := by
  apply UInt64.toNat_inj.mp
  have e : (x.toNat <<< 1 ||| 1) = x.toNat <<< 1 + 1 :=
    (Nat.shiftLeft_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) x.toNat).symm
  simp only [boxed, UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    show (1 : UInt64).toNat = 1 from rfl, show 1 % 64 = 1 from rfl]
  rw [Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega), e, Nat.shiftLeft_eq]
  omega

/-- `nat_result` reads an answer rightly where the answer is below 2^63: from an array of limbs in memory
it gives back the tagged word for the number those limbs are, and changes nothing. The limbs may have zero
limbs on top, as the arithmetic can leave them. -/
theorem natResult_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State) (extra : Nat)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs)
    (fits : Runtime.Big.value limbs < 9223372036854775808) :
    program.call outside (limbs.size + extra + 10) "nat_result" [array, UInt64.ofNat limbs.size] s
      = .ok (.gave (UInt64.ofNat (2 * Runtime.Big.value limbs + 1)), s) := by
  have elements := holds.2.2
  have run := trimmed_runs outside array limbs s small elements limbs.size extra (Nat.le_refl _)
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := value_trimCount limbs limbs.size (Runtime.Big.tail_of_le limbs _ (Nat.le_refl _))
  have hle := trimCount_le limbs limbs.size
  generalize hc : trimCount limbs limbs.size = c at hl hv hle
  rcases c with _ | _ | _ | c
  · have v0 : Runtime.Big.value limbs = 0 := hv
    have hl0 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 0, s, l) := hl
    rw [v0]
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl0, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]
  · have size1 : 0 < limbs.size := by omega
    have hl1 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 1, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 size1
    have v1 : Runtime.Big.value limbs = limbs[0].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size1]
    have fin : boxed limbs[0].toUInt64 = UInt64.ofNat (2 * Runtime.Big.value limbs + 1) := by
      rw [v1]
      have lt := limbs[0].toNat_lt
      have := boxed_small limbs[0].toUInt64 (by simp; omega)
      simpa using this
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl1, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, r0, unbox_boxed]
    simpa [boxed] using fin
  · have size2 : 1 < limbs.size := by omega
    have hl2 : runAll program outside (limbs.size + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat limbs.size]) = .ok (.gave 2, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 (by omega)
    have r1 : readBytes s.memory (array + 24 + 8) 8 = .ok (boxed limbs[1].toUInt64) := by
      rw [UInt64.add_assoc]; exact elements 1 size2
    have v2 : Runtime.Big.value limbs = limbs[0].toNat + 4294967296 * limbs[1].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size2, show 0 < limbs.size by omega]
    have l0 := limbs[0].toNat_lt
    have l1 := limbs[1].toNat_lt
    have h1 : limbs[1].toUInt64 < 2147483648 := by
      rw [UInt64.lt_iff_toNat_lt]; simp; omega
    have both : ((limbs[1].toUInt64 <<< 32) ||| limbs[0].toUInt64).toNat = Runtime.Big.value limbs := by
      rw [Runtime.Big.two_limbs_word _ _ (by simp; omega) (by simp; omega), v2]; simp; omega
    have fin : boxed ((limbs[1].toUInt64 <<< 32) ||| limbs[0].toUInt64)
        = UInt64.ofNat (2 * Runtime.Big.value limbs + 1) := by
      rw [← both]; exact boxed_small _ (by rw [both]; exact fits)
    simp [Program.call, find_natResult, find_trimmed, natResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl2, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, Expr.and, Expr.lt, top, r0, r1, unbox_boxed, h1]
    simpa [boxed] using fin
  · exfalso
    have topd := trimCount_top limbs limbs.size (c + 2) hc
    have big : 4294967296 ^ 2 ≤ 4294967296 ^ (c + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have one : 4294967296 ^ (c + 2) * 1 ≤ 4294967296 ^ (c + 2) * Runtime.Big.digit limbs (c + 2) :=
      Nat.mul_le_mul_left _ (by omega)
    have lower : Runtime.Big.lower limbs (c + 2 + 1)
        = Runtime.Big.lower limbs (c + 2) + 4294967296 ^ (c + 2) * Runtime.Big.digit limbs (c + 2) := rfl
    have hv' : Runtime.Big.value limbs = Runtime.Big.lower limbs (c + 2 + 1) := hv
    rw [Nat.mul_one] at one
    have sq : (4294967296 : Nat) ^ 2 = 18446744073709551616 := by decide
    generalize 4294967296 ^ (c + 2) = P at *
    omega

theorem find_natFrom : program.functions.find? (fun f => f.name == "nat_from") = some natFrom := rfl

/-- `nat_from`, which every operation on natural numbers ends with: from the array the arithmetic returned
it gives back the tagged word for the number in it, where that is below 2^63, and gives the array up. What
giving up does is the allocator's; nothing else changes. -/
theorem natFrom_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s after : State)
    (extra : Nat) (unused : UInt64)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs)
    (fits : Runtime.Big.value limbs < 9223372036854775808)
    (dec : outside "lean_dec" [array] s = .ok (unused, after)) :
    program.call outside (limbs.size + extra + 12) "nat_from" [array] s
      = .ok (.gave (UInt64.ofNat (2 * Runtime.Big.value limbs + 1)), after) := by
  have size := holds.2.1
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "nat_result" natResult _ s _ _ find_natResult
    (natResult_word outside array limbs s extra small holds fits)
  simp [Program.call, find_natFrom, find_natResult, natFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
    sizeOf, drop, size]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl, dec]

/-! ## An integer that arrives as a tagged word -/

theorem find_intSign : program.functions.find? (fun f => f.name == "int_sign") = some intSign := rfl
theorem find_intLimbs : program.functions.find? (fun f => f.name == "int_limbs") = some intLimbs := rfl

/-- An integer from -2^31 to 2^31 - 1 as compiled Lean holds it: its 32 bits, as a tagged word. This is
`lean_box((unsigned)n)` in `<lean/lean.h>`; the bits above the 32 are zero, whatever the sign. -/
def intWord (i : Int) : UInt64 := boxed (UInt64.ofNat (i % 4294967296).toNat)

/-- The 32 bits of an integer in that range, as a number. -/
theorem bits_lt (i : Int) : (i % 4294967296).toNat < 4294967296 := by omega

theorem intWord_toNat (i : Int) : (intWord i).toNat = 2 * (i % 4294967296).toNat + 1 := by
  have lt := bits_lt i
  rw [intWord, boxed_small _ (by simp only [UInt64.toNat_ofNat']; omega)]
  simp only [UInt64.toNat_ofNat']
  omega

theorem intWord_tagged (i : Int) : intWord i &&& 1 ≠ 0 := by
  intro h
  have := congrArg UInt64.toNat h
  rw [UInt64.toNat_and, intWord_toNat, show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod] at this
  have z : (0 : UInt64).toNat = 0 := rfl
  omega

/-- `int_sign` of a tagged word is bit 32 of it: the top bit of the 32 it holds. -/
theorem intSign_tagged (outside : Outside) (fuel : Nat) (o : UInt64) (s : State) (tagged : o &&& 1 ≠ 0) :
    program.call outside (fuel + 4) "int_sign" [o] s = .ok (.gave ((o >>> 32) &&& 1), s) := by
  simp [Program.call, find_intSign, intSign, runAll, Stmt.run, Expr.run, Op.run, bind, put, isWord, Expr.ne,
    Expr.and, Expr.shr, tagged]
  rfl

/-- `int_sign` says rightly whether an integer that arrives as a tagged word is below zero. -/
theorem intSign_word (outside : Outside) (fuel : Nat) (i : Int) (s : State)
    (lo : -2147483648 ≤ i) (hi : i < 2147483648) :
    program.call outside (fuel + 4) "int_sign" [intWord i] s = .ok (.gave (if i < 0 then 1 else 0), s) := by
  rw [intSign_tagged outside fuel _ s (intWord_tagged i)]
  have bit : (intWord i >>> 32) &&& 1 = if i < 0 then 1 else 0 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, intWord_toNat, show (1 : UInt64).toNat = 1 from rfl,
      Nat.and_one_is_mod, show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
    split
    · show _ = 1
      omega
    · show _ = 0
      omega
  rw [bit]

/-- What a tagged word holds without its sign: its 32 bits, or for a word whose top bit of those is set, what
they are the negation of within 32 bits. -/
def magnitude (o : UInt64) : UInt64 :=
  if (2147483648 : UInt64) ≤ (o >>> 1) &&& 4294967295 then -((o >>> 1) &&& 4294967295) &&& 4294967295
  else (o >>> 1) &&& 4294967295

/-- For an integer in the range a tagged word holds, that is the integer without its sign. -/
theorem magnitude_intWord (i : Int) (lo : -2147483648 ≤ i) (hi : i < 2147483648) :
    magnitude (intWord i) = UInt64.ofNat i.natAbs := by
  have low : ((intWord i >>> 1) &&& 4294967295).toNat = (i % 4294967296).toNat := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, intWord_toNat,
      show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
      show (1 : UInt64).toNat % 64 = 1 from rfl, Nat.shiftRight_eq_div_pow]
    omega
  apply UInt64.toNat_inj.mp
  unfold magnitude
  split
  · rename_i h
    rw [UInt64.le_iff_toNat_le, low] at h
    rw [UInt64.toNat_and, UInt64.toNat_neg, low, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat', show UInt64.size = 18446744073709551616 from rfl]
    have t : (2147483648 : UInt64).toNat = 2147483648 := rfl
    omega
  · rename_i h
    rw [UInt64.le_iff_toNat_le, low] at h
    rw [low, UInt64.toNat_ofNat']
    have t : (2147483648 : UInt64).toNat = 2147483648 := rfl
    omega

/-- `int_limbs` hands the arithmetic the limbs of what a tagged word holds without its sign. -/
theorem intLimbs_tagged (outside : Outside) (fuel : Nat) (o array : UInt64) (s s' : State) (tagged : o &&& 1 ≠ 0)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (magnitude o)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 26) "int_limbs" [o] s = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (magnitude o))
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (magnitude o)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  obtain ⟨memory, run, holds, frame⟩ := limbsOfWord_array outside fuel (magnitude o) array s s' alloc
  obtain ⟨l, hl⟩ := runAll_of_call program outside (fuel + 20) "limbs_of_word" limbsOfWord [magnitude o] s _ _
    find_limbsOfWord run
  refine ⟨memory, ?_, holds, frame⟩
  by_cases neg : (2147483648 : UInt64) ≤ (o >>> 1) &&& 4294967295
  · have m : magnitude o = -((o >>> 1) &&& 4294967295) &&& 4294967295 := by simp [magnitude, neg]
    have nlt : ¬ (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_lt.mpr neg
    rw [m] at hl
    simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, nlt]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]
  · have m : magnitude o = (o >>> 1) &&& 4294967295 := by simp [magnitude, neg]
    have lt : (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_le.mp neg
    rw [m] at hl
    simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, lt]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]

/-- `int_limbs` hands the arithmetic the right limbs for an integer that arrives as a tagged word: those of
the integer without its sign, with no zero limb on top. -/
theorem intLimbs_word (outside : Outside) (fuel : Nat) (i : Int) (array : UInt64) (s s' : State)
    (lo : -2147483648 ≤ i) (hi : i < 2147483648)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (UInt64.ofNat i.natAbs)).size)] s
      = .ok (array, s')) :
    ∃ memory,
      program.call outside (fuel + 26) "int_limbs" [intWord i] s
        = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array (wordLimbs (UInt64.ofNat i.natAbs))
      ∧ Runtime.Big.value (wordLimbs (UInt64.ofNat i.natAbs)) = i.natAbs
      ∧ ∀ p, (∀ k, k < 24 + 8 * (wordLimbs (UInt64.ofNat i.natAbs)).size → array + UInt64.ofNat k ≠ p) →
          memory p = s'.memory p := by
  rw [← magnitude_intWord i lo hi] at alloc ⊢
  obtain ⟨memory, run, holds, frame⟩ := intLimbs_tagged outside fuel _ array s s' (intWord_tagged i) alloc
  refine ⟨memory, run, holds, ?_, frame⟩
  rw [wordLimbs_value, magnitude_intWord i lo hi, UInt64.toNat_ofNat']
  omega

/-! ## Reading an integer answer that fits in a tagged word -/

theorem find_intResult : program.functions.find? (fun f => f.name == "int_result") = some intResult := rfl
theorem find_intFrom : program.functions.find? (fun f => f.name == "int_from") = some intFrom := rfl

/-- The number in the first `n` limbs is the number in those `trimmed` keeps. -/
theorem lower_trimCount (limbs : Runtime.Big.Limbs) (n : Nat) :
    Runtime.Big.lower limbs n = Runtime.Big.lower limbs (trimCount limbs n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold trimCount
    split
    · rename_i z
      have d : Runtime.Big.digit limbs n = 0 := by simp [Runtime.Big.digit, z]
      rw [← ih]
      show Runtime.Big.lower limbs n + 4294967296 ^ n * Runtime.Big.digit limbs n = _
      rw [d, Nat.mul_zero, Nat.add_zero]
    · rfl

/-- The integer with a size and a sign, the sign as the program passes it: a word that is zero for none. -/
def withSign (negative : UInt64) (size : Nat) : Int := if negative = 0 then (size : Int) else -(size : Int)

theorem intWord_nat (m : Nat) (h : m < 4294967296) : intWord (m : Int) = boxed (UInt64.ofNat m) := by
  rw [intWord, show ((m : Int) % 4294967296).toNat = m from by omega]

theorem intWord_neg (x : UInt64) (pos : 0 < x.toNat) (h : x.toNat ≤ 2147483648) :
    intWord (-(x.toNat : Int)) = boxed (-x &&& 4294967295) := by
  rw [intWord]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_neg, show (4294967295 : UInt64).toNat = 2 ^ 32 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat', show UInt64.size = 18446744073709551616 from rfl]
  omega

/-- `int_result` reads an answer rightly where the answer is in the range a tagged word holds: from a sign
and the first `n` limbs of an array in memory it gives back the tagged word for that integer, and changes
nothing. The limbs may have zero limbs on top, and a sign on zero comes back as plain zero. -/
theorem intResult_word (outside : Outside) (array negative : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (n extra : Nat) (small : limbs.size < 2305843009213693952)
    (elements : ∀ i, (h : i < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * i)) 8 = .ok (boxed limbs[i].toUInt64))
    (hn : n ≤ limbs.size)
    (lo : -2147483648 ≤ withSign negative (Runtime.Big.lower limbs n))
    (hi : withSign negative (Runtime.Big.lower limbs n) < 2147483648) :
    program.call outside (n + extra + 10) "int_result" [negative, array, UInt64.ofNat n] s
      = .ok (.gave (intWord (withSign negative (Runtime.Big.lower limbs n))), s) := by
  have run := trimmed_runs outside array limbs s small elements n extra hn
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := lower_trimCount limbs n
  have hle := trimCount_le limbs n
  have bound : Runtime.Big.lower limbs n ≤ 2147483648 := by
    by_cases z : negative = 0 <;> simp [withSign, z] at lo hi <;> omega
  generalize hc : trimCount limbs n = c at hl hv hle
  rcases c with _ | _ | c
  · have v0 : Runtime.Big.lower limbs n = 0 := hv
    have hl0 : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n]) = .ok (.gave 0, s, l) := hl
    have w : withSign negative 0 = 0 := by unfold withSign; split <;> rfl
    rw [v0, w]
    simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      hl0, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]
    rfl
  · have size1 : 0 < limbs.size := by omega
    have hl1 : runAll program outside (n + extra + 8) trimmed.body s
        (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n]) = .ok (.gave 1, s, l) := hl
    have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed limbs[0].toUInt64) := elements 0 size1
    have v1 : Runtime.Big.lower limbs n = limbs[0].toNat := by
      rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, size1]
    have nz : limbs[0].toNat ≠ 0 := by
      have := trimCount_top limbs n 0 hc
      simpa [Runtime.Big.digit, Array.getD, size1] using this
    rw [v1] at lo hi bound ⊢
    by_cases z : negative = 0
    · subst z
      have w : withSign 0 limbs[0].toNat = (limbs[0].toNat : Int) := rfl
      rw [w] at hi ⊢
      have h1 : limbs[0].toUInt64 < 2147483648 := by
        rw [UInt64.lt_iff_toNat_lt]; simp; omega
      have fin : boxed limbs[0].toUInt64 = intWord (limbs[0].toNat : Int) := by
        rw [intWord_nat _ (by omega)]
        congr 1
        apply UInt64.toNat_inj.mp
        simp
      simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        hl1, box, Expr.eq, Expr.or, Expr.shl]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
        unbox, Expr.shr, Expr.and, Expr.lt, top, r0, unbox_boxed, h1]
      simpa [boxed] using fin
    · have w : withSign negative limbs[0].toNat = -(limbs[0].toNat : Int) := by simp [withSign, z]
      rw [w] at lo hi ⊢
      have h1 : limbs[0].toUInt64 ≤ 2147483648 := by
        rw [UInt64.le_iff_toNat_le]; simp; omega
      have fin : boxed (-limbs[0].toUInt64 &&& 4294967295) = intWord (-(limbs[0].toNat : Int)) := by
        have := intWord_neg limbs[0].toUInt64 (by simp; omega) (by simp; omega)
        simpa using this.symm
      simp [Program.call, find_intResult, find_trimmed, intResult, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        hl1, box, Expr.eq, Expr.or, Expr.shl]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
        unbox, Expr.shr, Expr.and, Expr.lt, Expr.le, Expr.ne, top, low32, r0, unbox_boxed, h1, z]
      simpa [boxed] using fin
  · exfalso
    have topd := trimCount_top limbs n (c + 1) hc
    have big : 4294967296 ^ 1 ≤ 4294967296 ^ (c + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have one : 4294967296 ^ (c + 1) * 1 ≤ 4294967296 ^ (c + 1) * Runtime.Big.digit limbs (c + 1) :=
      Nat.mul_le_mul_left _ (by omega)
    have lower : Runtime.Big.lower limbs (c + 1 + 1)
        = Runtime.Big.lower limbs (c + 1) + 4294967296 ^ (c + 1) * Runtime.Big.digit limbs (c + 1) := rfl
    have hv' : Runtime.Big.lower limbs n = Runtime.Big.lower limbs (c + 1 + 1) := hv
    rw [Nat.mul_one] at one
    rw [Nat.pow_one] at big
    generalize 4294967296 ^ (c + 1) = P at *
    omega

theorem lower_congr (a b : Runtime.Big.Limbs) (n : Nat)
    (h : ∀ i, i < n → Runtime.Big.digit a i = Runtime.Big.digit b i) :
    Runtime.Big.lower a n = Runtime.Big.lower b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show Runtime.Big.lower a n + 4294967296 ^ n * Runtime.Big.digit a n
      = Runtime.Big.lower b n + 4294967296 ^ n * Runtime.Big.digit b n
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

/-- An array without its last element is the number in the limbs below that one. -/
theorem value_pop_lower (a : Runtime.Big.Limbs) :
    Runtime.Big.value a.pop = Runtime.Big.lower a (a.size - 1) := by
  rw [← Runtime.Big.lower_size a.pop, Array.size_pop]
  exact lower_congr _ _ _ (fun i hi => by
    simp [Runtime.Big.digit, Array.getD, hi, show i < a.size by omega])

/-- `int_from`, which every operation on integers ends with: from the array the arithmetic returned, limbs
and then a sign, it gives back the tagged word for the integer in it (`signedValue`, which is what
`Runtime/BigProofs.lean` proves the arithmetic's answers about), where that is in the range a tagged word
holds, and gives the array up. What giving up does is the allocator's; nothing else changes. -/
theorem intFrom_word (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s after : State)
    (n extra : Nat) (unused : UInt64)
    (small : limbs.size < 2305843009213693952)
    (holds : ArrayOf s.memory array limbs) (size : limbs.size = n + 1)
    (lo : -2147483648 ≤ Runtime.Big.signedValue limbs) (hi : Runtime.Big.signedValue limbs < 2147483648)
    (dec : outside "lean_dec" [array] s = .ok (unused, after)) :
    program.call outside (n + extra + 14) "int_from" [array] s
      = .ok (.gave (intWord (Runtime.Big.signedValue limbs)), after) := by
  have hsize := holds.2.1
  rw [size] at hsize
  have read := holds.2.2 n (by omega)
  rw [← below_count] at read
  have pop : Runtime.Big.value limbs.pop = Runtime.Big.lower limbs n := by
    rw [value_pop_lower, size, Nat.add_sub_cancel]
  generalize hc : UInt64.ofNat (n + 1) = c at hsize read
  have cpos : c ≠ 0 := by
    intro z
    have := congrArg UInt64.toNat (hc.trans z)
    simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
    omega
  have cless : UInt64.ofNat n = c - 1 := by
    rw [← hc]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
    omega
  by_cases top : limbs[n]'(by omega) = 0
  · have sv : Runtime.Big.signedValue limbs = withSign 0 (Runtime.Big.lower limbs n) := by
      simp [Runtime.Big.signedValue, Runtime.Big.intOf, size, Array.getD, top, pop, withSign]
    rw [sv] at lo hi ⊢
    obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult
      (intResult_word outside array 0 limbs s n extra small holds.2.2 (by omega) lo hi)
    rw [cless] at hl
    have hz : (limbs[n]'(by omega)).toUInt64 = 0 := by rw [top]; rfl
    simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hz, hl, dec,
      show boxed 0 >>> 1 = 0 from by decide]
  · have nz : (limbs[n]'(by omega)).toUInt64 ≠ 0 := fun h => top (UInt32.toNat_inj.mp (by
      have := congrArg UInt64.toNat h
      simpa using this))
    have sv : Runtime.Big.signedValue limbs = withSign 1 (Runtime.Big.lower limbs n) := by
      simp [Runtime.Big.signedValue, Runtime.Big.intOf, size, Array.getD, top, pop, withSign]
    rw [sv] at lo hi ⊢
    obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult
      (intResult_word outside array 1 limbs s n extra small holds.2.2 (by omega) lo hi)
    rw [cless] at hl
    simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hl, dec,
      unbox_boxed, nz]

/-! ## Running a function a statement at a time

A function with a loop in it is taken a statement at a time, so that the loop is met as a whole and what is
proved of it by induction can be used. -/

theorem runAll_on (p : Program) (outside : Outside) (fuel : Nat) (st : Stmt) (rest : List Stmt)
    (s s1 : State) (locals locals1 : Locals)
    (h : Stmt.run p outside fuel st s locals = .ok (.on, s1, locals1)) :
    runAll p outside (fuel + 1) (st :: rest) s locals = runAll p outside fuel rest s1 locals1 := by
  rw [runAll, h]
  rfl

theorem runAll_gave (p : Program) (outside : Outside) (fuel : Nat) (st : Stmt) (rest : List Stmt)
    (s s1 : State) (locals locals1 : Locals) (value : UInt64)
    (h : Stmt.run p outside fuel st s locals = .ok (.gave value, s1, locals1)) :
    runAll p outside (fuel + 1) (st :: rest) s locals = .ok (.gave value, s1, locals1) := by
  rw [runAll, h]
  rfl

/-- What running a function's body says about calling it by name. -/
theorem call_of_runAll (p : Program) (outside : Outside) (fuel : Nat) (function : String) (f : Function)
    (arguments : List UInt64) (s after : State) (ending : Ending) (locals : Locals)
    (found : p.functions.find? (fun f => f.name == function) = some f)
    (run : runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments)
      = .ok (ending, after, locals)) :
    p.call outside fuel function arguments s = .ok (ending, after) := by
  unfold Program.call
  rw [found]
  dsimp only
  rw [run]
  rfl

/-- A statement that fails is where the run of statements fails. -/
theorem runAll_fails (p : Program) (outside : Outside) (fuel : Nat) (st : Stmt) (rest : List Stmt)
    (s : State) (locals : Locals) (why : String)
    (h : Stmt.run p outside fuel st s locals = .error why) :
    runAll p outside (fuel + 1) (st :: rest) s locals = .error why := by
  rw [runAll, h]
  rfl

/-- What a failing body says about calling the function by name, and back. -/
theorem call_fails (p : Program) (outside : Outside) (fuel : Nat) (function : String) (f : Function)
    (arguments : List UInt64) (s : State) (why : String)
    (found : p.functions.find? (fun f => f.name == function) = some f)
    (run : runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments) = .error why) :
    p.call outside fuel function arguments s = .error why := by
  unfold Program.call
  rw [found]
  dsimp only
  rw [run]
  rfl

theorem runAll_of_fails (p : Program) (outside : Outside) (fuel : Nat) (function : String) (f : Function)
    (arguments : List UInt64) (s : State) (why : String)
    (found : p.functions.find? (fun f => f.name == function) = some f)
    (call : p.call outside fuel function arguments s = .error why) :
    runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments) = .error why := by
  unfold Program.call at call
  rw [found] at call
  dsimp only at call
  cases run : runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments) with
  | error e =>
    rw [run] at call
    injection call with same
    rw [← same]
  | ok r =>
    rw [run] at call
    cases call

/-! ## Rooms that share no byte -/

/-- A read sees only the bytes it reads. -/
theorem readBytes_congr (m m' : UInt64 → Option UInt8) (x : UInt64) (n : Nat)
    (same : ∀ i, i < n → m (x + UInt64.ofNat i) = m' (x + UInt64.ofNat i)) :
    readBytes m x n = readBytes m' x n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have here : m x = m' x := by simpa using same 0 (by omega)
    have further : readBytes m (x + 1) n = readBytes m' (x + 1) n :=
      ih (x + 1) (fun i hi => by
        have := same (i + 1) (by omega)
        rwa [show x + UInt64.ofNat (i + 1) = x + 1 + UInt64.ofNat i from by
          rw [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm (UInt64.ofNat i)]; rfl] at this)
    simp only [readBytes, here, further]

theorem offset_add (a : UInt64) (x i : Nat) :
    a + UInt64.ofNat x + UInt64.ofNat i = a + UInt64.ofNat (x + i) := by
  rw [UInt64.ofNat_add, UInt64.add_assoc]

/-- A write inside one room leaves a read inside another, which shares no byte with it, as it was. -/
theorem read_across (memory : UInt64 → Option UInt8) (a b word : UInt64) (x c roomA y n roomB : Nat)
    (hx : x + c ≤ roomA) (hy : y + n ≤ roomB)
    (apart : ∀ k, k < roomA → ∀ j, j < roomB → a + UInt64.ofNat k ≠ b + UInt64.ofNat j) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word c) (b + UInt64.ofNat y) n
      = readBytes memory (b + UInt64.ofNat y) n := by
  refine readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => ?_)
  rw [offset_add, offset_add]
  exact apart _ (by omega) _ (by omega)

/-- A write and a read at two runs counted from one address, which do not meet. -/
theorem read_beside (memory : UInt64 → Option UInt8) (a word : UInt64) (x c y n : Nat)
    (hx : x + c < 9223372036854775808) (hy : y + n < 9223372036854775808) (apart : x + c ≤ y ∨ y + n ≤ x) :
    readBytes (writeBytes memory (a + UInt64.ofNat x) word c) (a + UInt64.ofNat y) n
      = readBytes memory (a + UInt64.ofNat y) n := by
  refine readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk h => ?_)
  rw [offset_add, offset_add] at h
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  have := a.toNat_lt
  omega

/-- A write inside a room leaves everything outside the room as it was. -/
theorem write_within (memory : UInt64 → Option UInt8) (a word q : UInt64) (x c room : Nat) (h : x + c ≤ room)
    (outside : ∀ k, k < room → a + UInt64.ofNat k ≠ q) :
    writeBytes memory (a + UInt64.ofNat x) word c q = memory q := by
  refine writeBytes_other _ _ _ _ _ (fun k hk => ?_)
  rw [offset_add]
  exact outside _ (by omega)

/-- Reading back four bytes that were just written, of a word that fits in them. -/
theorem read_part (memory : UInt64 → Option UInt8) (a word : UInt64) (h : word.toNat < 4294967296) :
    readBytes (writeBytes memory a word 4) a 4 = .ok word := by
  obtain ⟨r, hr, hvalue⟩ := readBytes_writeBytes memory a word 4 (by omega)
  have : r = word := UInt64.toNat_inj.mp (by
    rw [hvalue, show 2 ^ (8 * 4) = 4294967296 from rfl]
    omega)
  rw [hr, this]

/-! ## A number that is an object -/

theorem find_checked : program.functions.find? (fun f => f.name == "checked") = some checked := rfl
theorem find_limbsOfObject :
    program.functions.find? (fun f => f.name == "limbs_of_object") = some limbsOfObject := rfl

/-- A big number at an address, as much of it as this program makes and reads: a header that says it is a
number, four bytes of sign, four bytes of count, and that many limbs of four bytes each. -/
def ObjectOf (memory : UInt64 → Option UInt8) (o negative : UInt64) (limbs : Runtime.Big.Limbs) : Prop :=
  (∃ header, readBytes memory o 8 = .ok header ∧ header >>> 56 = UInt64.ofNat numberKind) ∧
  readBytes memory (o + 8) 4 = .ok negative ∧
  readBytes memory (o + 12) 4 = .ok (UInt64.ofNat limbs.size) ∧
  ∀ i, (h : i < limbs.size) → readBytes memory (o + UInt64.ofNat (16 + 4 * i)) 4 = .ok limbs[i].toUInt64

/-- The address of the limb below a count that is not zero. -/
theorem below_object_count (o : UInt64) (n : Nat) :
    o + 16 + (UInt64.ofNat (n + 1) - 1) * 4 = o + UInt64.ofNat (16 + 4 * n) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_sub, UInt64.toNat_ofNat',
    show (16 : UInt64).toNat = 16 from rfl, show (4 : UInt64).toNat = 4 from rfl,
    show (1 : UInt64).toNat = 1 from rfl]
  omega

theorem limb_nonzero (limb : UInt32) (h : limb ≠ 0) : limb.toUInt64 ≠ 0 := fun z => h (UInt32.toNat_inj.mp (by
  have := congrArg UInt64.toNat z
  simpa using this))

/-- `checked` passes an object that is a number as this program makes them, with a top limb that is not zero
and a sign of 0 or 1, and gives its count. It reads the object and changes nothing. -/
theorem checked_runs (outside : Outside) (fuel : Nat) (o negative : UInt64) (limbs : Runtime.Big.Limbs)
    (s : State) (holds : ObjectOf s.memory o negative limbs) (small : limbs.size < 4294967296)
    (top : Runtime.Big.digit limbs (limbs.size - 1) ≠ 0) (sign : negative ≤ 1) :
    program.call outside (fuel + 6) "checked" [o] s = .ok (.gave (UInt64.ofNat limbs.size), s) := by
  obtain ⟨⟨header, hread, hkind⟩, hneg, hcount, hlimbs⟩ := holds
  have pos : 0 < limbs.size := by
    refine Nat.pos_of_ne_zero (fun z => top ?_)
    simp [Runtime.Big.digit, Array.getD, z]
  obtain ⟨m, size⟩ : ∃ m, limbs.size = m + 1 := ⟨limbs.size - 1, by omega⟩
  have read := hlimbs m (by omega)
  rw [← below_object_count] at read
  have nz : (limbs[m]'(by omega)).toUInt64 ≠ 0 := limb_nonzero _ (fun z => top (by
    simp [Runtime.Big.digit, Array.getD, size, z]))
  rw [size] at hcount ⊢
  generalize hc : UInt64.ofNat (m + 1) = c at hcount read
  have cpos : c ≠ 0 := by
    intro z
    have := congrArg UInt64.toNat (hc.trans z)
    simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
    omega
  simp [Program.call, find_checked, checked, runAll, Stmt.run, Expr.run, Op.run, bind, put, countOf, negativeOf,
    objectLimb, Expr.or, Expr.ne, Expr.eq, Expr.lt, Expr.shr, hread, hcount]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hkind, hneg, read, cpos, nz,
    sign]

/-! ## Copying an object's limbs into an array -/

/-- The loop in `limbs_of_object`, under a name of its own. -/
def copyLoop (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :=
  Stmt.run p outside fuel (.loop (Expr.lt "i" "count")
    [.store ("array" + 24 + "i" * 8) (box (objectLimb "o" "i")), .set "i" ("i" + 1)]) s locals

theorem element_address (array : UInt64) (i : Nat) :
    array + 24 + UInt64.ofNat i * 8 = array + UInt64.ofNat (24 + 8 * i) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (24 : UInt64).toNat = 24 from rfl,
    show (8 : UInt64).toNat = 8 from rfl]
  omega

theorem limb_address (o : UInt64) (i : Nat) : o + 16 + UInt64.ofNat i * 4 = o + UInt64.ofNat (16 + 4 * i) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (16 : UInt64).toNat = 16 from rfl,
    show (4 : UInt64).toNat = 4 from rfl]
  omega

/-- The loop, from any limb on: it writes each limb of the object from there up into the array as a tagged
word, and nothing else. What it has written below stays, and so does everything outside the array's room. The
array's room and the object share no byte. -/
theorem copy_loop (p : Program) (outside : Outside) (o array : UInt64) (limbs : Runtime.Big.Limbs)
    (small : limbs.size < 4294967296)
    (apart : ∀ k, k < 24 + 8 * limbs.size → ∀ j, j < 16 + 4 * limbs.size →
      array + UInt64.ofNat k ≠ o + UInt64.ofNat j) :
    ∀ (remaining i : Nat) (s : State) (locals : Locals) (extra : Nat), i + remaining = limbs.size →
      locals "i" = some (UInt64.ofNat i) → locals "count" = some (UInt64.ofNat limbs.size) →
      locals "o" = some o → locals "array" = some array →
      (∀ j, (h : j < limbs.size) →
        readBytes s.memory (o + UInt64.ofNat (16 + 4 * j)) 4 = .ok limbs[j].toUInt64) →
      ∃ memory after,
        copyLoop p outside (remaining + extra + 6) s locals = .ok (.on, { s with memory := memory }, after)
        ∧ after "array" = some array
        ∧ (∀ j, (h : j < limbs.size) → i ≤ j →
            readBytes memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
        ∧ (∀ x n, x + n ≤ 24 + 8 * i →
            readBytes memory (array + UInt64.ofNat x) n = readBytes s.memory (array + UInt64.ofNat x) n)
        ∧ ∀ q, (∀ k, k < 24 + 8 * limbs.size → array + UInt64.ofNat k ≠ q) → memory q = s.memory q := by
  intro remaining
  induction remaining with
  | zero =>
    intro i s locals extra hsum hi hcount ho harray hobj
    have e : i = limbs.size := by omega
    subst e
    refine ⟨s.memory, locals, ?_, harray, fun j h hij => absurd h (by omega), fun _ _ _ => rfl, fun _ _ => rfl⟩
    simp [copyLoop, Stmt.run, Expr.run, Op.run, Expr.lt, hi, hcount]
    rfl
  | succ remaining ih =>
    intro i s locals extra hsum hi hcount ho harray hobj
    have ilt : i < limbs.size := by omega
    have limb := hobj i ilt
    have ea := element_address array i
    have lt : UInt64.ofNat i < UInt64.ofNat limbs.size := by
      rw [UInt64.lt_iff_toNat_lt]
      simp only [UInt64.toNat_ofNat']
      omega
    have next : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by rw [UInt64.ofNat_add]; rfl
    rw [← limb_address] at limb
    generalize hiw : UInt64.ofNat i = iw at hi limb lt next ea
    generalize hcw : UInt64.ofNat limbs.size = cw at hcount lt
    obtain ⟨memory, after, hrun, harr, helems, hbelow, hframe⟩ := ih (i + 1)
      { s with memory := writeBytes s.memory (array + 24 + iw * 8) (limbs[i].toUInt64 <<< 1 ||| 1) 8 }
      (put locals "i" (some (iw + 1))) extra (by omega) (by rw [← next]; simp [put])
      (by rw [hcw]; simp [put, hcount]) (by simp [put, ho]) (by simp [put, harray])
      (fun j h => by
        rw [ea]
        exact (read_across _ array o _ (24 + 8 * i) 8 (24 + 8 * limbs.size) (16 + 4 * j) 4
          (16 + 4 * limbs.size) (by omega) (by omega) apart).trans (hobj j h))
    refine ⟨memory, after, ?_, harr, ?_, ?_, ?_⟩
    · unfold copyLoop at hrun ⊢
      rw [show remaining + 1 + extra + 6 = (remaining + extra + 6) + 1 from by omega, Mini.Alloc.loop_turn]
      generalize hround : Stmt.run p outside (remaining + extra + 6) (.loop (Expr.lt "i" "count")
        [.store ("array" + 24 + "i" * 8) (box (objectLimb "o" "i")), .set "i" ("i" + 1)]) = round at hrun ⊢
      simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.or, Expr.shl, box, objectLimb, hi, hcount, ho,
        harray, limb, lt]
      simp [Bind.bind, Except.bind, hrun]
    · intro j h hij
      by_cases e : j = i
      · subst e
        exact (hbelow (24 + 8 * j) 8 (by omega)).trans (by
          rw [ea]
          exact readBytes_writeBytes_word _ _ _)
      · exact helems j h (by omega)
    · intro x n hxn
      exact (hbelow x n (by omega)).trans (by
        rw [ea]
        exact read_beside _ array _ (24 + 8 * i) 8 x n (by omega) (by omega) (by omega))
    · intro q hq
      exact (hframe q hq).trans (by
        rw [ea]
        exact write_within _ array _ q (24 + 8 * i) 8 (24 + 8 * limbs.size) (by omega) hq)

/-- `limbs_of_object` hands the arithmetic the limbs of an object: given room for an array that shares no
byte with the object, it leaves there an array holding the object's limbs, does nothing C leaves open, and
changes nothing outside that room. -/
theorem limbsOfObject_array (outside : Outside) (extra : Nat) (o array : UInt64) (limbs : Runtime.Big.Limbs)
    (s s' : State) (small : limbs.size < 4294967296)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * limbs.size)] s = .ok (array, s'))
    (object : ∀ j, (h : j < limbs.size) →
      readBytes s'.memory (o + UInt64.ofNat (16 + 4 * j)) 4 = .ok limbs[j].toUInt64)
    (apart : ∀ k, k < 24 + 8 * limbs.size → ∀ j, j < 16 + 4 * limbs.size →
      array + UInt64.ofNat k ≠ o + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (limbs.size + extra + 14) "limbs_of_object" [o, UInt64.ofNat limbs.size] s
        = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array limbs
      ∧ ∀ q, (∀ k, k < 24 + 8 * limbs.size → array + UInt64.ofNat k ≠ q) → memory q = s'.memory q := by
  have room : (24 : UInt64) + UInt64.ofNat limbs.size * 8 = UInt64.ofNat (24 + 8 * limbs.size) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (24 : UInt64).toNat = 24 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    omega
  rw [← room] at alloc
  obtain ⟨l0, hl0⟩ := runAll_of_call program outside _ "array_new" arrayNew _ s _ _ find_arrayNew
    (arrayNew_runs outside (limbs.size + extra + 2) (UInt64.ofNat limbs.size) array s s' alloc)
  generalize hlocals : bind (fun _ => none) ["o", "count"] [o, UInt64.ofNat limbs.size] = locals
  have lo : locals "o" = some o := by rw [← hlocals]; simp [bind, put]
  have lcount : locals "count" = some (UInt64.ofNat limbs.size) := by rw [← hlocals]; simp [bind, put]
  generalize hs1 : ({ s' with memory := headed s'.memory array (UInt64.ofNat limbs.size) } : State) = s1
  have s1memory : s1.memory = headed s'.memory array (UInt64.ofNat limbs.size) := by rw [← hs1]
  have st1 : Stmt.run program outside (limbs.size + extra + 13) (.call (some "array") "array_new" ["count"]) s
      locals = .ok (.on, s1, put locals "array" (some array)) := by
    have hl0' : runAll program outside (limbs.size + extra + 12) arrayNew.body s
        (bind (fun _ => none) arrayNew.parameters [UInt64.ofNat limbs.size]) = .ok (.gave array, s1, l0) := by
      rw [← hs1]; exact hl0
    simp [Stmt.run, find_arrayNew, Expr.run, lcount, hl0']
    rfl
  have st2 : Stmt.run program outside (limbs.size + extra + 12) (.set "i" 0) s1
      (put locals "array" (some array)) = .ok (.on, s1, put (put locals "array" (some array)) "i" (some 0)) := by
    simp [Stmt.run, Expr.run]
    rfl
  obtain ⟨memory, after, hloop, harr, helems, hbelow, hframe⟩ := copy_loop program outside o array limbs small
    apart limbs.size 0 s1 (put (put locals "array" (some array)) "i" (some 0)) (extra + 5) (by omega)
    (by simp [put]) (by simp [put, lcount]) (by simp [put, lo]) (by simp [put])
    (fun j h => by
      rw [s1memory]
      refine (readBytes_congr _ _ _ _ (fun i hi => ?_)).trans (object j h)
      refine headed_outside _ _ _ _ (24 + 8 * limbs.size) (by omega) (fun k hk => ?_)
      rw [offset_add]
      exact apart k hk _ (by omega))
  have st4 : Stmt.run program outside (limbs.size + extra + 10) (.give "array") { s1 with memory := memory } after
      = .ok (.gave array, { s1 with memory := memory }, after) := by
    simp [Stmt.run, Expr.run, harr]
    rfl
  refine ⟨memory, ?_, ⟨?_, ?_, fun i h => helems i h (Nat.zero_le _)⟩, ?_⟩
  · have same : ({ s1 with memory := memory } : State) = { s' with memory := memory } := by rw [← hs1]
    rw [← same]
    refine call_of_runAll program outside _ "limbs_of_object" limbsOfObject _ s _ _ after find_limbsOfObject ?_
    show runAll program outside (limbs.size + extra + 13 + 1) [.call (some "array") "array_new" ["count"],
      .set "i" 0, .loop (Expr.lt "i" "count")
        [.store ("array" + 24 + "i" * 8) (box (objectLimb "o" "i")), .set "i" ("i" + 1)],
      .give "array"] s (bind (fun _ => none) ["o", "count"] [o, UInt64.ofNat limbs.size]) = _
    rw [hlocals]
    exact (runAll_on _ _ _ _ _ _ _ _ _ st1).trans ((runAll_on _ _ (limbs.size + extra + 12) _ _ _ _ _ _ st2).trans
      ((runAll_on _ _ (limbs.size + extra + 11) _ _ _ _ _ _ hloop).trans
        (runAll_gave _ _ (limbs.size + extra + 10) _ _ _ _ _ _ _ st4)))
  · have := hbelow 0 8 (by omega)
    rw [s1memory] at this
    exact (by simpa using this : readBytes memory array 8 = _).trans (headed_header _ _ _)
  · have := hbelow 8 8 (by omega)
    rw [s1memory] at this
    exact this.trans (headed_size _ _ _)
  · intro q hq
    exact (hframe q hq).trans (by
      rw [s1memory]
      exact headed_outside _ _ _ _ (24 + 8 * limbs.size) (by omega) hq)

/-- An object whose bytes an allocation left alone still holds what it held. -/
theorem object_kept (memory memory' : UInt64 → Option UInt8) (o negative : UInt64) (limbs : Runtime.Big.Limbs)
    (holds : ObjectOf memory o negative limbs)
    (kept : ∀ j, j < 16 + 4 * limbs.size → memory' (o + UInt64.ofNat j) = memory (o + UInt64.ofNat j)) :
    ObjectOf memory' o negative limbs := by
  obtain ⟨⟨header, hread, hkind⟩, hneg, hcount, hlimbs⟩ := holds
  refine ⟨⟨header, ?_, hkind⟩, ?_, ?_, fun i h => ?_⟩
  · exact (readBytes_congr _ _ _ _ (fun i hi => kept i (by omega))).trans hread
  · exact (readBytes_congr _ _ (o + UInt64.ofNat 8) _ (fun i hi => by
      rw [offset_add]; exact kept _ (by omega))).trans hneg
  · exact (readBytes_congr _ _ (o + UInt64.ofNat 12) _ (fun i hi => by
      rw [offset_add]; exact kept _ (by omega))).trans hcount
  · exact (readBytes_congr _ _ _ _ (fun k hk => by
      rw [offset_add]; exact kept _ (by omega))).trans (hlimbs i h)

/-- `nat_limbs` passes an object that is a natural number of 2^63 or more on to `limbs_of_object`: what that
gives it gives, and where that does not return neither does it. -/
theorem natLimbs_object_pass (outside : Outside) (extra : Nat) (o : UInt64) (limbs : Runtime.Big.Limbs)
    (s : State) (pointer : o &&& 1 = 0) (holds : ObjectOf s.memory o 0 limbs)
    (small : limbs.size < 4294967296) (nozero : Runtime.Big.Trimmed limbs)
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs) :
    (∀ why, program.call outside (limbs.size + extra + 14) "limbs_of_object" [o, UInt64.ofNat limbs.size] s
        = .error why →
      program.call outside (limbs.size + extra + 20) "nat_limbs" [o] s = .error why) ∧
    ∀ array after, program.call outside (limbs.size + extra + 14) "limbs_of_object" [o, UInt64.ofNat limbs.size] s
        = .ok (.gave array, after) →
      program.call outside (limbs.size + extra + 20) "nat_limbs" [o] s = .ok (.gave array, after) := by
  have vlt := Runtime.Big.value_lt_pow limbs
  have size2 : 2 ≤ limbs.size := by
    have : limbs.size = 0 ∨ limbs.size = 1 ∨ 2 ≤ limbs.size := by omega
    rcases this with e | e | e
    · rw [e, Nat.pow_zero] at vlt; omega
    · rw [e, Nat.pow_one] at vlt; omega
    · exact e
  have topd : Runtime.Big.digit limbs (limbs.size - 1) ≠ 0 := nozero.resolve_left (by omega)
  obtain ⟨lc, hlc⟩ := runAll_of_call program outside _ "checked" checked _ s _ _ find_checked
    (checked_runs outside (limbs.size + extra + 11) o 0 limbs s holds small topd (by decide))
  have hneg := holds.2.1
  have r1 : readBytes s.memory (o + 16 + 4) 4 = .ok (limbs[1]'(by omega)).toUInt64 := by
    rw [UInt64.add_assoc]; exact holds.2.2.2 1 (by omega)
  have ge2 : (2 : UInt64) ≤ UInt64.ofNat limbs.size := by
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_ofNat', show (2 : UInt64).toNat = 2 from rfl]
    omega
  have third : ((if UInt64.ofNat limbs.size = 2 then (1 : UInt64) else 0)
      &&& (if (limbs[1]'(by omega)).toUInt64 < 2147483648 then 1 else 0)) = 0 := by
    by_cases c2 : UInt64.ofNat limbs.size = 2
    · have e : limbs.size = 2 := by
        have := congrArg UInt64.toNat c2
        simp only [UInt64.toNat_ofNat', show (2 : UInt64).toNat = 2 from rfl] at this
        omega
      have ls := Runtime.Big.lower_size limbs
      rw [e] at ls
      have v2 : Runtime.Big.value limbs
          = (limbs[0]'(by omega)).toNat + 4294967296 * (limbs[1]'(by omega)).toNat := by
        rw [← ls]
        simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, show 1 < limbs.size by omega,
          show 0 < limbs.size by omega]
      have h1 : ¬ (limbs[1]'(by omega)).toUInt64 < 2147483648 := by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl]
        have := (limbs[0]'(by omega)).toNat_lt
        omega
      simp [h1]
    · simp [c2]
  refine ⟨fun why run => ?_, fun array after run => ?_⟩
  · have hlo := runAll_of_fails program outside _ "limbs_of_object" limbsOfObject _ s why find_limbsOfObject run
    generalize UInt64.ofNat limbs.size = cw at hlc hlo ge2 third
    simp [Program.call, find_natLimbs, find_checked, find_limbsOfObject, natLimbs, runAll, Stmt.run, Expr.run,
      Op.run, bind, put, isWord, negativeOf, objectLimb, Number.top, Expr.ne, Expr.and, Expr.or, Expr.eq, Expr.lt,
      pointer, hlc]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hneg, r1, ge2, third, hlo]
  · obtain ⟨lo, hlo⟩ := runAll_of_call program outside _ "limbs_of_object" limbsOfObject _ s _ _
      find_limbsOfObject run
    generalize UInt64.ofNat limbs.size = cw at hlc hlo ge2 third
    simp [Program.call, find_natLimbs, find_checked, find_limbsOfObject, natLimbs, runAll, Stmt.run, Expr.run,
      Op.run, bind, put, isWord, negativeOf, objectLimb, Number.top, Expr.ne, Expr.and, Expr.or, Expr.eq, Expr.lt,
      pointer, hlc]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hneg, r1, ge2, third, hlo]

/-- A natural number of 2^63 or more arrives as an object. `nat_limbs` hands the arithmetic its limbs: given
room for an array that shares no byte with the object, where making the room left the object alone, it
leaves there an array holding the object's limbs and changes nothing outside that room. -/
theorem natLimbs_object (outside : Outside) (extra : Nat) (o array : UInt64) (limbs : Runtime.Big.Limbs)
    (s s' : State) (pointer : o &&& 1 = 0) (holds : ObjectOf s.memory o 0 limbs)
    (small : limbs.size < 4294967296) (nozero : Runtime.Big.Trimmed limbs)
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * limbs.size)] s = .ok (array, s'))
    (kept : ∀ j, j < 16 + 4 * limbs.size → s'.memory (o + UInt64.ofNat j) = s.memory (o + UInt64.ofNat j))
    (apart : ∀ k, k < 24 + 8 * limbs.size → ∀ j, j < 16 + 4 * limbs.size →
      array + UInt64.ofNat k ≠ o + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (limbs.size + extra + 20) "nat_limbs" [o] s
        = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array limbs
      ∧ ∀ q, (∀ k, k < 24 + 8 * limbs.size → array + UInt64.ofNat k ≠ q) → memory q = s'.memory q := by
  obtain ⟨memory, run, array_, frame⟩ := limbsOfObject_array outside extra o array limbs s s' small alloc
    (object_kept s.memory s'.memory o 0 limbs holds kept).2.2.2 apart
  exact ⟨memory, (natLimbs_object_pass outside extra o limbs s pointer holds small nozero big).2 array _ run,
    array_, frame⟩

/-- `int_sign` of an object is the sign it holds. -/
theorem intSign_object (outside : Outside) (fuel : Nat) (o negative : UInt64) (limbs : Runtime.Big.Limbs)
    (s : State) (pointer : o &&& 1 = 0) (holds : ObjectOf s.memory o negative limbs) :
    program.call outside (fuel + 4) "int_sign" [o] s = .ok (.gave negative, s) := by
  have hneg := holds.2.1
  simp [Program.call, find_intSign, intSign, runAll, Stmt.run, Expr.run, Op.run, bind, put, isWord, negativeOf,
    Expr.ne, Expr.and, Expr.shr, pointer, hneg]
  rfl

/-- `int_limbs` passes an object that is an integer outside the range a tagged word holds on to
`limbs_of_object`: what that gives it gives, and where that does not return neither does it. -/
theorem intLimbs_object_pass (outside : Outside) (extra : Nat) (o negative : UInt64)
    (limbs : Runtime.Big.Limbs) (s : State) (pointer : o &&& 1 = 0)
    (holds : ObjectOf s.memory o negative limbs) (small : limbs.size < 4294967296)
    (nozero : Runtime.Big.Trimmed limbs) (sign : negative ≤ 1)
    (range : withSign negative (Runtime.Big.value limbs) < -2147483648
      ∨ 2147483648 ≤ withSign negative (Runtime.Big.value limbs)) :
    (∀ why, program.call outside (limbs.size + extra + 14) "limbs_of_object" [o, UInt64.ofNat limbs.size] s
        = .error why →
      program.call outside (limbs.size + extra + 19) "int_limbs" [o] s = .error why) ∧
    ∀ array after, program.call outside (limbs.size + extra + 14) "limbs_of_object" [o, UInt64.ofNat limbs.size] s
        = .ok (.gave array, after) →
      program.call outside (limbs.size + extra + 19) "int_limbs" [o] s = .ok (.gave array, after) := by
  have vbig : 2147483648 ≤ Runtime.Big.value limbs := by
    by_cases z : negative = 0 <;> simp [withSign, z] at range <;> omega
  have vlt := Runtime.Big.value_lt_pow limbs
  have size1 : 1 ≤ limbs.size := by
    refine Nat.pos_of_ne_zero (fun e => ?_)
    rw [e, Nat.pow_zero] at vlt
    omega
  have topd : Runtime.Big.digit limbs (limbs.size - 1) ≠ 0 := nozero.resolve_left (by omega)
  obtain ⟨lc, hlc⟩ := runAll_of_call program outside _ "checked" checked _ s _ _ find_checked
    (checked_runs outside (limbs.size + extra + 10) o negative limbs s holds small topd sign)
  have hneg := holds.2.1
  have r0 : readBytes s.memory (o + 16) 4 = .ok (limbs[0]'(by omega)).toUInt64 := holds.2.2.2 0 (by omega)
  refine ⟨fun why run => ?fails, fun array after run => ?gives⟩
  case' fails =>
    have hlo := runAll_of_fails program outside _ "limbs_of_object" limbsOfObject _ s why find_limbsOfObject run
  case' gives =>
    obtain ⟨lo, hlo⟩ := runAll_of_call program outside _ "limbs_of_object" limbsOfObject _ s _ _
      find_limbsOfObject run
  all_goals
    by_cases one : limbs.size = 1
    · have c1 : UInt64.ofNat limbs.size = 1 := by rw [one]; rfl
      have ls := Runtime.Big.lower_size limbs
      rw [one] at ls
      have v1 : Runtime.Big.value limbs = (limbs[0]'(by omega)).toNat := by
        rw [← ls]
        simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, show 0 < limbs.size by omega]
      have h1 : (2147483648 : UInt64) ≤ (limbs[0]'(by omega)).toUInt64 := by
        rw [UInt64.le_iff_toNat_le]
        simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl]
        omega
      rw [c1] at hlc hlo
      by_cases z : negative = 0
      · simp [Program.call, find_intLimbs, find_checked, find_limbsOfObject, intLimbs, runAll, Stmt.run, Expr.run,
          Op.run, bind, put, isWord, negativeOf, objectLimb, Number.top, Expr.ne, Expr.and, Expr.or, Expr.eq,
          Expr.lt, pointer, hlc]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hneg, r0, h1, z, hlo]
      · have far : (limbs[0]'(by omega)).toUInt64 ≠ 2147483648 := by
          intro e
          have := congrArg UInt64.toNat e
          simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl] at this
          simp [withSign, z] at range
          omega
        simp [Program.call, find_intLimbs, find_checked, find_limbsOfObject, intLimbs, runAll, Stmt.run, Expr.run,
          Op.run, bind, put, isWord, negativeOf, objectLimb, Number.top, Expr.ne, Expr.and, Expr.or, Expr.eq,
          Expr.lt, pointer, hlc]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hneg, r0, h1, z, far,
          hlo]
    · have cn : UInt64.ofNat limbs.size ≠ 1 := by
        intro e
        have := congrArg UInt64.toNat e
        simp only [UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl] at this
        omega
      generalize UInt64.ofNat limbs.size = cw at hlc hlo cn
      simp [Program.call, find_intLimbs, find_checked, find_limbsOfObject, intLimbs, runAll, Stmt.run, Expr.run,
        Op.run, bind, put, isWord, negativeOf, objectLimb, Number.top, Expr.ne, Expr.and, Expr.or, Expr.eq, Expr.lt,
        pointer, hlc]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cn, hlo]

/-- An integer outside the range a tagged word holds arrives as an object. `int_limbs` hands the arithmetic
its limbs, on the same terms as `nat_limbs` does for a natural number. -/
theorem intLimbs_object (outside : Outside) (extra : Nat) (o array negative : UInt64)
    (limbs : Runtime.Big.Limbs) (s s' : State) (pointer : o &&& 1 = 0)
    (holds : ObjectOf s.memory o negative limbs) (small : limbs.size < 4294967296)
    (nozero : Runtime.Big.Trimmed limbs) (sign : negative ≤ 1)
    (range : withSign negative (Runtime.Big.value limbs) < -2147483648
      ∨ 2147483648 ≤ withSign negative (Runtime.Big.value limbs))
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * limbs.size)] s = .ok (array, s'))
    (kept : ∀ j, j < 16 + 4 * limbs.size → s'.memory (o + UInt64.ofNat j) = s.memory (o + UInt64.ofNat j))
    (apart : ∀ k, k < 24 + 8 * limbs.size → ∀ j, j < 16 + 4 * limbs.size →
      array + UInt64.ofNat k ≠ o + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (limbs.size + extra + 19) "int_limbs" [o] s
        = .ok (.gave array, { s' with memory := memory })
      ∧ ArrayOf memory array limbs
      ∧ ∀ q, (∀ k, k < 24 + 8 * limbs.size → array + UInt64.ofNat k ≠ q) → memory q = s'.memory q := by
  obtain ⟨memory, run, array_, frame⟩ := limbsOfObject_array outside extra o array limbs s s' small alloc
    (object_kept s.memory s'.memory o negative limbs holds kept).2.2.2 apart
  exact ⟨memory,
    (intLimbs_object_pass outside extra o negative limbs s pointer holds small nozero sign range).2 array _ run,
    array_, frame⟩

/-! ## Making an object of an answer -/

theorem find_bigNew : program.functions.find? (fun f => f.name == "big_new") = some bigNew := rfl

/-- The header of a number with one reference. -/
def numberHeader : UInt64 := UInt64.ofNat (1 + numberKind * 2 ^ 56)

/-- The loop in `big_new`, under a name of its own. -/
def fillLoop (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :=
  Stmt.run p outside fuel (.loop (Expr.lt "i" "count")
    [.storePart 4 ("o" + 16 + "i" * 4) (limbAt "array" "i"), .set "i" ("i" + 1)]) s locals

/-- The loop, from any limb on: it writes each of the array's limbs from there up to the count into the
object, four bytes each, and nothing else. The object's room and the array share no byte. -/
theorem fill_loop (p : Program) (outside : Outside) (o array : UInt64) (limbs : Runtime.Big.Limbs) (count : Nat)
    (hcount : count ≤ limbs.size) (small : limbs.size < 4294967296)
    (apart : ∀ k, k < 16 + 4 * count → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∀ (remaining i : Nat) (s : State) (locals : Locals) (extra : Nat), i + remaining = count →
      locals "i" = some (UInt64.ofNat i) → locals "count" = some (UInt64.ofNat count) →
      locals "o" = some o → locals "array" = some array →
      (∀ j, (h : j < limbs.size) →
        readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64)) →
      ∃ memory after,
        fillLoop p outside (remaining + extra + 6) s locals = .ok (.on, { s with memory := memory }, after)
        ∧ after "o" = some o
        ∧ (∀ j, (h : j < limbs.size) → i ≤ j → j < count →
            readBytes memory (o + UInt64.ofNat (16 + 4 * j)) 4 = .ok limbs[j].toUInt64)
        ∧ (∀ x n, x + n ≤ 16 + 4 * i →
            readBytes memory (o + UInt64.ofNat x) n = readBytes s.memory (o + UInt64.ofNat x) n)
        ∧ ∀ q, (∀ k, k < 16 + 4 * count → o + UInt64.ofNat k ≠ q) → memory q = s.memory q := by
  intro remaining
  induction remaining with
  | zero =>
    intro i s locals extra hsum hi hc ho harray helements
    have e : i = count := by omega
    subst e
    refine ⟨s.memory, locals, ?_, ho, fun j h hij hjc => absurd hjc (by omega), fun _ _ _ => rfl, fun _ _ => rfl⟩
    simp [fillLoop, Stmt.run, Expr.run, Op.run, Expr.lt, hi, hc]
    rfl
  | succ remaining ih =>
    intro i s locals extra hsum hi hc ho harray helements
    have ilt : i < limbs.size := by omega
    have limb := helements i ilt
    have eo := limb_address o i
    have lt : UInt64.ofNat i < UInt64.ofNat count := by
      rw [UInt64.lt_iff_toNat_lt]
      simp only [UInt64.toNat_ofNat']
      omega
    have next : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by rw [UInt64.ofNat_add]; rfl
    rw [← element_address] at limb
    generalize hiw : UInt64.ofNat i = iw at hi limb lt next eo
    generalize hcw : UInt64.ofNat count = cw at hc lt
    obtain ⟨memory, after, hrun, hafter, hlimbs, hbelow, hframe⟩ := ih (i + 1)
      { s with memory := writeBytes s.memory (o + 16 + iw * 4) limbs[i].toUInt64 4 }
      (put locals "i" (some (iw + 1))) extra (by omega) (by rw [← next]; simp [put])
      (by rw [hcw]; simp [put, hc]) (by simp [put, ho]) (by simp [put, harray])
      (fun j h => by
        rw [eo]
        exact (read_across _ o array _ (16 + 4 * i) 4 (16 + 4 * count) (24 + 8 * j) 8
          (24 + 8 * limbs.size) (by omega) (by omega) apart).trans (helements j h))
    refine ⟨memory, after, ?_, hafter, ?_, ?_, ?_⟩
    · unfold fillLoop at hrun ⊢
      rw [show remaining + 1 + extra + 6 = (remaining + extra + 6) + 1 from by omega, Mini.Alloc.loop_turn]
      generalize hround : Stmt.run p outside (remaining + extra + 6) (.loop (Expr.lt "i" "count")
        [.storePart 4 ("o" + 16 + "i" * 4) (limbAt "array" "i"), .set "i" ("i" + 1)]) = round at hrun ⊢
      simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, Expr.shr, limbAt, unbox, hi, hc, ho, harray, limb, lt]
      simp [Bind.bind, Except.bind, unbox_boxed, hrun]
    · intro j h hij hjc
      by_cases e : j = i
      · subst e
        exact (hbelow (16 + 4 * j) 4 (by omega)).trans (by
          rw [eo]
          exact read_part _ _ _ (by simp; exact limbs[j].toNat_lt))
      · exact hlimbs j h (by omega) hjc
    · intro x n hxn
      exact (hbelow x n (by omega)).trans (by
        rw [eo]
        exact read_beside _ o _ (16 + 4 * i) 4 x n (by omega) (by omega) (by omega))
    · intro q hq
      exact (hframe q hq).trans (by
        rw [eo]
        exact write_within _ o _ q (16 + 4 * i) 4 (16 + 4 * count) (by omega) hq)

/-- `big_new` makes the object for a sign and the first `count` limbs of an array: given room that shares no
byte with the array, it leaves there an object holding that sign and those limbs, does nothing C leaves
open, and changes nothing outside that room. -/
theorem bigNew_object (outside : Outside) (extra : Nat) (negative array o : UInt64) (limbs : Runtime.Big.Limbs)
    (count : Nat) (s s' : State) (hcount : count ≤ limbs.size) (small : limbs.size < 4294967296)
    (sign : negative ≤ 1)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * count)] s = .ok (o, s'))
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s'.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (apart : ∀ k, k < 16 + 4 * count → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (count + extra + 16) "big_new" [negative, array, UInt64.ofNat count] s
        = .ok (.gave o, { s' with memory := memory })
      ∧ ObjectOf memory o negative (limbs.extract 0 count)
      ∧ ∀ q, (∀ k, k < 16 + 4 * count → o + UInt64.ofNat k ≠ q) → memory q = s'.memory q := by
  have room : (16 : UInt64) + UInt64.ofNat count * 4 = UInt64.ofNat (16 + 4 * count) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (16 : UInt64).toNat = 16 from rfl,
      show (4 : UInt64).toNat = 4 from rfl]
    omega
  rw [← room] at alloc
  have fits : UInt64.ofNat count ≤ 4294967295 := by
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_ofNat', show (4294967295 : UInt64).toNat = 4294967295 from rfl]
    omega
  have cnat : (UInt64.ofNat count).toNat < 4294967296 := by
    simp only [UInt64.toNat_ofNat']
    omega
  have nnat : negative.toNat < 4294967296 := by
    rw [UInt64.le_iff_toNat_le] at sign
    have : (1 : UInt64).toNat = 1 := rfl
    omega
  generalize hcw : UInt64.ofNat count = cw at alloc fits cnat
  generalize hlocals : bind (fun _ => none) ["negative", "array", "count"] [negative, array, cw] = locals
  have lneg : locals "negative" = some negative := by rw [← hlocals]; simp [bind, put]
  have larray : locals "array" = some array := by rw [← hlocals]; simp [bind, put]
  have lcount : locals "count" = some cw := by rw [← hlocals]; simp [bind, put]
  generalize hm : writeBytes (writeBytes (writeBytes s'.memory o numberHeader 8) (o + 8) negative 4) (o + 12) cw 4
    = written
  have outsideRoom : ∀ q, (∀ k, k < 16 + 4 * count → o + UInt64.ofNat k ≠ q) → written q = s'.memory q := by
    intro q hq
    rw [← hm]
    exact (write_within _ o _ q 12 4 (16 + 4 * count) (by omega) hq).trans
      ((write_within _ o _ q 8 4 (16 + 4 * count) (by omega) hq).trans
        (writeBytes_other _ _ _ _ _ (fun k hk => hq k (by omega))))
  have st0 : Stmt.run program outside (count + extra + 15) (.branch (Expr.lt low32 "count") [outOfMemory] []) s
      locals = .ok (.on, s, locals) := by
    simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, low32, lcount, fits]
    rfl
  have st1 : Stmt.run program outside (count + extra + 14)
      (.callOther (some "o") "lean_alloc_object" [16 + "count" * 4]) s locals
      = .ok (.on, s', put locals "o" (some o)) := by
    simp [Stmt.run, Expr.run, Op.run, lcount, alloc]
    rfl
  have st2 : Stmt.run program outside (count + extra + 13) (.store "o" (header numberKind)) s'
      (put locals "o" (some o))
      = .ok (.on, { s' with memory := writeBytes s'.memory o numberHeader 8 }, put locals "o" (some o)) := by
    simp [Stmt.run, Expr.run, header, put]
    rfl
  have st3 : Stmt.run program outside (count + extra + 12) (.storePart 4 ("o" + 8) "negative")
      { s' with memory := writeBytes s'.memory o numberHeader 8 } (put locals "o" (some o))
      = .ok (.on, { s' with memory := writeBytes (writeBytes s'.memory o numberHeader 8) (o + 8) negative 4 },
          put locals "o" (some o)) := by
    simp [Stmt.run, Expr.run, Op.run, put, lneg]
    rfl
  have st4 : Stmt.run program outside (count + extra + 11) (.storePart 4 ("o" + 12) "count")
      { s' with memory := writeBytes (writeBytes s'.memory o numberHeader 8) (o + 8) negative 4 }
      (put locals "o" (some o))
      = .ok (.on, { s' with memory := written }, put locals "o" (some o)) := by
    rw [← hm]
    simp [Stmt.run, Expr.run, Op.run, put, lcount]
    rfl
  have st5 : Stmt.run program outside (count + extra + 10) (.set "i" 0) { s' with memory := written }
      (put locals "o" (some o))
      = .ok (.on, { s' with memory := written }, put (put locals "o" (some o)) "i" (some 0)) := by
    simp [Stmt.run, Expr.run]
    rfl
  obtain ⟨memory, after, hloop, hafter, hlimbs, hbelow, hframe⟩ := fill_loop program outside o array limbs count
    hcount small apart count 0 { s' with memory := written } (put (put locals "o" (some o)) "i" (some 0))
    (extra + 3) (by omega) (by simp [put]) (by rw [hcw]; simp [put, lcount]) (by simp [put])
    (by simp [put, larray])
    (fun j h => by
      refine (readBytes_congr _ _ _ _ (fun i hi => ?_)).trans (elements j h)
      refine outsideRoom _ (fun k hk => ?_)
      rw [offset_add]
      exact apart k hk _ (by omega))
  have st7 : Stmt.run program outside (count + extra + 8) (.give "o") { s' with memory := memory } after
      = .ok (.gave o, { s' with memory := memory }, after) := by
    simp [Stmt.run, Expr.run, hafter]
    rfl
  have size : (limbs.extract 0 count).size = count := by simp; omega
  refine ⟨memory, ?_, ⟨⟨numberHeader, ?_, by decide⟩, ?_, ?_, fun i h => ?_⟩, ?_⟩
  · refine call_of_runAll program outside _ "big_new" bigNew _ s _ _ after find_bigNew ?_
    show runAll program outside (count + extra + 15 + 1) [.branch (Expr.lt low32 "count") [outOfMemory] [],
      .callOther (some "o") "lean_alloc_object" [16 + "count" * 4],
      .store "o" (header numberKind),
      .storePart 4 ("o" + 8) "negative",
      .storePart 4 ("o" + 12) "count",
      .set "i" 0,
      .loop (Expr.lt "i" "count")
        [.storePart 4 ("o" + 16 + "i" * 4) (limbAt "array" "i"), .set "i" ("i" + 1)],
      .give "o"] s (bind (fun _ => none) ["negative", "array", "count"] [negative, array, cw]) = _
    rw [hlocals]
    exact (runAll_on _ _ _ _ _ _ _ _ _ st0).trans ((runAll_on _ _ (count + extra + 14) _ _ _ _ _ _ st1).trans
      ((runAll_on _ _ (count + extra + 13) _ _ _ _ _ _ st2).trans
        ((runAll_on _ _ (count + extra + 12) _ _ _ _ _ _ st3).trans
          ((runAll_on _ _ (count + extra + 11) _ _ _ _ _ _ st4).trans
            ((runAll_on _ _ (count + extra + 10) _ _ _ _ _ _ st5).trans
              ((runAll_on _ _ (count + extra + 9) _ _ _ _ _ _ hloop).trans
                (runAll_gave _ _ (count + extra + 8) _ _ _ _ _ _ _ st7)))))))
  · have := hbelow 0 8 (by omega)
    refine (by simpa using this : readBytes memory o 8 = readBytes written o 8).trans ?_
    rw [← hm]
    have h0 : readBytes (writeBytes (writeBytes (writeBytes s'.memory o numberHeader 8) (o + 8) negative 4)
        (o + 12) cw 4) (o + UInt64.ofNat 0) 8 = .ok numberHeader :=
      (read_beside _ o _ 12 4 0 8 (by omega) (by omega) (by omega)).trans
        ((read_beside _ o _ 8 4 0 8 (by omega) (by omega) (by omega)).trans
          (by simpa using readBytes_writeBytes_word s'.memory o numberHeader))
    simpa using h0
  · refine (hbelow 8 4 (by omega)).trans ?_
    show readBytes written (o + UInt64.ofNat 8) 4 = _
    rw [← hm]
    exact (read_beside _ o _ 12 4 8 4 (by omega) (by omega) (by omega)).trans (read_part _ _ _ nnat)
  · refine (hbelow 12 4 (by omega)).trans ?_
    show readBytes written (o + UInt64.ofNat 12) 4 = _
    rw [← hm, size, hcw]
    exact read_part _ _ _ cnat
  · rw [size] at h
    have := hlimbs i (by omega) (Nat.zero_le _) h
    simpa using this
  · intro q hq
    exact (hframe q hq).trans (outsideRoom q hq)

/-! ## An answer too large for a tagged word -/

/-- The first `n` limbs of an array without the zero limbs on top: what the object for an answer holds. -/
def keptLimbs (limbs : Runtime.Big.Limbs) (n : Nat) : Runtime.Big.Limbs := limbs.extract 0 (trimCount limbs n)

theorem keptLimbs_size (limbs : Runtime.Big.Limbs) (n : Nat) (hn : n ≤ limbs.size) :
    (keptLimbs limbs n).size = trimCount limbs n := by
  have := trimCount_le limbs n
  simp [keptLimbs]
  omega

theorem keptLimbs_digit (limbs : Runtime.Big.Limbs) (n i : Nat) (hn : n ≤ limbs.size)
    (hi : i < trimCount limbs n) : Runtime.Big.digit (keptLimbs limbs n) i = Runtime.Big.digit limbs i := by
  have := trimCount_le limbs n
  have inside : i < limbs.size := by omega
  have within : i < min (trimCount limbs n) limbs.size := by omega
  simp [Runtime.Big.digit, Array.getD, keptLimbs, inside, within]

/-- They are the number in the first `n` limbs. -/
theorem keptLimbs_value (limbs : Runtime.Big.Limbs) (n : Nat) (hn : n ≤ limbs.size) :
    Runtime.Big.value (keptLimbs limbs n) = Runtime.Big.lower limbs n := by
  rw [← Runtime.Big.lower_size, keptLimbs_size _ _ hn, lower_trimCount limbs n]
  exact lower_congr _ _ _ (fun i hi => keptLimbs_digit limbs n i hn hi)

/-- And the top one is not zero, the rule every object that leaves this program keeps. -/
theorem keptLimbs_trimmed (limbs : Runtime.Big.Limbs) (n : Nat) (hn : n ≤ limbs.size) :
    Runtime.Big.Trimmed (keptLimbs limbs n) := by
  rw [Runtime.Big.Trimmed, keptLimbs_size _ _ hn]
  cases h : trimCount limbs n with
  | zero => exact Or.inl rfl
  | succ m =>
    refine Or.inr ?_
    rw [Nat.add_sub_cancel, keptLimbs_digit limbs n m hn (by omega)]
    exact trimCount_top limbs n m h

/-- An array whose bytes an allocation left alone still holds its limbs. -/
theorem elements_kept (memory memory' : UInt64 → Option UInt8) (array : UInt64) (limbs : Runtime.Big.Limbs)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (kept : ∀ j, j < 24 + 8 * limbs.size → memory' (array + UInt64.ofNat j) = memory (array + UInt64.ofNat j)) :
    ∀ j, (h : j < limbs.size) →
      readBytes memory' (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64) :=
  fun j h => (readBytes_congr _ _ _ _ (fun k hk => by
    rw [offset_add]; exact kept _ (by omega))).trans (elements j h)

theorem word_ne (c k : Nat) (hc : c < 4294967296) (hk : k < 4294967296) (h : c ≠ k) :
    UInt64.ofNat c ≠ UInt64.ofNat k := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_ofNat'] at this
  omega

/-- `nat_result` passes an answer of 2^63 or more on to `big_new`, with the count `trimmed` gave: what that
gives it gives, and where that does not return neither does it. -/
theorem natResult_pass (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (extra : Nat) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs) :
    (∀ why, program.call outside (limbs.size + extra + 16) "big_new"
        [0, array, UInt64.ofNat (trimCount limbs limbs.size)] s = .error why →
      program.call outside (limbs.size + extra + 22) "nat_result" [array, UInt64.ofNat limbs.size] s
        = .error why) ∧
    ∀ o after, program.call outside (limbs.size + extra + 16) "big_new"
        [0, array, UInt64.ofNat (trimCount limbs limbs.size)] s = .ok (.gave o, after) →
      program.call outside (limbs.size + extra + 22) "nat_result" [array, UInt64.ofNat limbs.size] s
        = .ok (.gave o, after) := by
  have run := trimmed_runs outside array limbs s (by omega) elements limbs.size (extra + 12) (Nat.le_refl _)
  rw [show limbs.size + (extra + 12) + 8 = limbs.size + extra + 20 from by omega] at run
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := value_trimCount limbs limbs.size (Runtime.Big.tail_of_le limbs _ (Nat.le_refl _))
  have hle := trimCount_le limbs limbs.size
  generalize trimCount limbs limbs.size = c at hl hv hle ⊢
  have lowlt := Runtime.Big.lower_lt limbs c
  have c2 : 2 ≤ c := by
    have : c = 0 ∨ c = 1 ∨ 2 ≤ c := by omega
    rcases this with e | e | e
    · subst e; rw [Nat.pow_zero] at lowlt; omega
    · subst e; rw [Nat.pow_one] at lowlt; omega
    · exact e
  have r1 : readBytes s.memory (array + 24 + 8) 8 = .ok (boxed (limbs[1]'(by omega)).toUInt64) := by
    rw [UInt64.add_assoc]; exact elements 1 (by omega)
  have n0 : UInt64.ofNat c ≠ 0 := word_ne c 0 (by omega) (by omega) (by omega)
  have n1 : UInt64.ofNat c ≠ 1 := word_ne c 1 (by omega) (by omega) (by omega)
  have third : ((if UInt64.ofNat c = 2 then (1 : UInt64) else 0)
      &&& (if (limbs[1]'(by omega)).toUInt64 < 2147483648 then 1 else 0)) = 0 := by
    by_cases e2 : UInt64.ofNat c = 2
    · have e : c = 2 := by
        have := congrArg UInt64.toNat e2
        simp only [UInt64.toNat_ofNat', show (2 : UInt64).toNat = 2 from rfl] at this
        omega
      rw [e] at hv
      have v2 : Runtime.Big.value limbs
          = (limbs[0]'(by omega)).toNat + 4294967296 * (limbs[1]'(by omega)).toNat := by
        rw [hv]
        simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, show 1 < limbs.size by omega,
          show 0 < limbs.size by omega]
      have h1 : ¬ (limbs[1]'(by omega)).toUInt64 < 2147483648 := by
        rw [UInt64.lt_iff_toNat_lt]
        simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl]
        have := (limbs[0]'(by omega)).toNat_lt
        omega
      simp [h1]
    · simp [e2]
  refine ⟨fun why made => ?_, fun o after made => ?_⟩
  · have hl2 := runAll_of_fails program outside _ "big_new" bigNew _ s why find_bigNew made
    generalize UInt64.ofNat c = cw at hl hl2 n0 n1 third
    simp [Program.call, find_natResult, find_trimmed, find_bigNew, natResult, runAll, Stmt.run, Expr.run, Op.run,
      bind, put, hl, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, Expr.and, Expr.lt, Number.top, r1, unbox_boxed, n0, n1, third, hl2]
  · obtain ⟨l2, hl2⟩ := runAll_of_call program outside _ "big_new" bigNew _ s _ _ find_bigNew made
    generalize UInt64.ofNat c = cw at hl hl2 n0 n1 third
    simp [Program.call, find_natResult, find_trimmed, find_bigNew, natResult, runAll, Stmt.run, Expr.run, Op.run,
      bind, put, hl, box, Expr.eq, Expr.or, Expr.shl]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run, limbAt,
      unbox, Expr.shr, Expr.and, Expr.lt, Number.top, r1, unbox_boxed, n0, n1, third, hl2]

/-- `nat_result` reads an answer rightly where the answer is 2^63 or more: from an array of limbs in memory,
given room that shares no byte with the array, where making the room left the array alone, it makes there an
object holding the array's limbs without the zero ones on top (`keptLimbs`, whose number is the array's and
whose top limb is not zero), and changes nothing outside that room. -/
theorem natResult_object (outside : Outside) (array o : UInt64) (limbs : Runtime.Big.Limbs) (s s' : State)
    (extra : Nat) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs limbs.size)] s = .ok (o, s'))
    (kept : ∀ j, j < 24 + 8 * limbs.size → s'.memory (array + UInt64.ofNat j) = s.memory (array + UInt64.ofNat j))
    (apart : ∀ k, k < 16 + 4 * trimCount limbs limbs.size → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (limbs.size + extra + 22) "nat_result" [array, UInt64.ofNat limbs.size] s
        = .ok (.gave o, { s' with memory := memory })
      ∧ ObjectOf memory o 0 (keptLimbs limbs limbs.size)
      ∧ ∀ q, (∀ k, k < 16 + 4 * trimCount limbs limbs.size → o + UInt64.ofNat k ≠ q) →
          memory q = s'.memory q := by
  have hle := trimCount_le limbs limbs.size
  obtain ⟨memory, made, object, frame⟩ := bigNew_object outside (limbs.size - trimCount limbs limbs.size + extra) 0
    array o limbs _ s s' hle small (by decide) alloc (elements_kept _ _ _ _ elements kept) apart
  rw [show trimCount limbs limbs.size + (limbs.size - trimCount limbs limbs.size + extra) + 16
    = limbs.size + extra + 16 from by omega] at made
  exact ⟨memory, (natResult_pass outside array limbs s extra small elements big).2 o _ made, object, frame⟩

/-- `int_result` passes an answer outside the range a tagged word holds on to `big_new`, with the count
`trimmed` gave: what that gives it gives, and where that does not return neither does it. -/
theorem intResult_pass (outside : Outside) (array negative : UInt64) (limbs : Runtime.Big.Limbs)
    (s : State) (n extra : Nat) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (hn : n ≤ limbs.size)
    (range : withSign negative (Runtime.Big.lower limbs n) < -2147483648
      ∨ 2147483648 ≤ withSign negative (Runtime.Big.lower limbs n)) :
    (∀ why, program.call outside (n + extra + 16) "big_new"
        [negative, array, UInt64.ofNat (trimCount limbs n)] s = .error why →
      program.call outside (n + extra + 21) "int_result" [negative, array, UInt64.ofNat n] s = .error why) ∧
    ∀ o after, program.call outside (n + extra + 16) "big_new"
        [negative, array, UInt64.ofNat (trimCount limbs n)] s = .ok (.gave o, after) →
      program.call outside (n + extra + 21) "int_result" [negative, array, UInt64.ofNat n] s
        = .ok (.gave o, after) := by
  have run := trimmed_runs outside array limbs s (by omega) elements n (extra + 11) hn
  rw [show n + (extra + 11) + 8 = n + extra + 19 from by omega] at run
  obtain ⟨l, hl⟩ := runAll_of_call program outside _ "trimmed" trimmed _ s _ _ find_trimmed run
  have hv := lower_trimCount limbs n
  have hle := trimCount_le limbs n
  have vbig : 2147483648 ≤ Runtime.Big.lower limbs n := by
    by_cases z : negative = 0 <;> simp [withSign, z] at range <;> omega
  generalize trimCount limbs n = c at hl hv hle ⊢
  have c1 : 1 ≤ c := by
    refine Nat.pos_of_ne_zero (fun e => ?_)
    subst e
    have : Runtime.Big.lower limbs 0 = 0 := rfl
    omega
  refine ⟨fun why made => ?fails, fun o after made => ?gives⟩
  case' fails =>
    have hl2 := runAll_of_fails program outside _ "big_new" bigNew _ s why find_bigNew made
  case' gives =>
    obtain ⟨l2, hl2⟩ := runAll_of_call program outside _ "big_new" bigNew _ s _ _ find_bigNew made
  all_goals
    by_cases one : c = 1
    · subst one
      have hl1 : runAll program outside (n + extra + 19) trimmed.body s
          (bind (fun _ => none) trimmed.parameters [array, UInt64.ofNat n]) = .ok (.gave 1, s, l) := hl
      have one' : UInt64.ofNat 1 = 1 := rfl
      rw [one'] at hl2
      have r0 : readBytes s.memory (array + 24) 8 = .ok (boxed (limbs[0]'(by omega)).toUInt64) :=
        elements 0 (by omega)
      have v1 : Runtime.Big.lower limbs n = (limbs[0]'(by omega)).toNat := by
        rw [hv]; simp [Runtime.Big.lower, Runtime.Big.digit, Array.getD, show 0 < limbs.size by omega]
      rw [v1] at range
      by_cases z : negative = 0
      · subst z
        have nlt : ¬ (limbs[0]'(by omega)).toUInt64 < 2147483648 := by
          rw [UInt64.lt_iff_toNat_lt]
          simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl]
          simp [withSign] at range
          omega
        simp [Program.call, find_intResult, find_trimmed, find_bigNew, intResult, runAll, Stmt.run, Expr.run,
          Op.run, bind, put, hl1, box, Expr.eq, Expr.or, Expr.shl]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run,
          limbAt, unbox, Expr.shr, Expr.and, Expr.lt, Expr.le, Expr.ne, Number.top, r0, unbox_boxed, nlt, hl2]
      · have nle : ¬ (limbs[0]'(by omega)).toUInt64 ≤ 2147483648 := by
          rw [UInt64.le_iff_toNat_le]
          simp only [UInt32.toNat_toUInt64, show (2147483648 : UInt64).toNat = 2147483648 from rfl]
          simp [withSign, z] at range
          omega
        simp [Program.call, find_intResult, find_trimmed, find_bigNew, intResult, runAll, Stmt.run, Expr.run,
          Op.run, bind, put, hl1, box, Expr.eq, Expr.or, Expr.shl]
        simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, Expr.run, Op.run,
          limbAt, unbox, Expr.shr, Expr.and, Expr.lt, Expr.le, Expr.ne, Number.top, r0, unbox_boxed, nle, z, hl2]
    · have n0 : UInt64.ofNat c ≠ 0 := word_ne c 0 (by omega) (by omega) (by omega)
      have n1 : UInt64.ofNat c ≠ 1 := word_ne c 1 (by omega) (by omega) one
      generalize UInt64.ofNat c = cw at hl hl2 n0 n1
      simp [Program.call, find_intResult, find_trimmed, find_bigNew, intResult, runAll, Stmt.run, Expr.run, Op.run,
        bind, put, hl, box, Expr.eq, Expr.or, Expr.shl]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, n0, n1, hl2]

/-- `int_result` reads an answer rightly where the answer is outside the range a tagged word holds: from a
sign and the first `n` limbs of an array, given room on the same terms as `nat_result`, it makes there an
object holding that sign and those limbs without the zero ones on top, and changes nothing outside that
room. -/
theorem intResult_object (outside : Outside) (array negative o : UInt64) (limbs : Runtime.Big.Limbs)
    (s s' : State) (n extra : Nat) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (hn : n ≤ limbs.size) (sign : negative ≤ 1)
    (range : withSign negative (Runtime.Big.lower limbs n) < -2147483648
      ∨ 2147483648 ≤ withSign negative (Runtime.Big.lower limbs n))
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs n)] s = .ok (o, s'))
    (kept : ∀ j, j < 24 + 8 * limbs.size → s'.memory (array + UInt64.ofNat j) = s.memory (array + UInt64.ofNat j))
    (apart : ∀ k, k < 16 + 4 * trimCount limbs n → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∃ memory,
      program.call outside (n + extra + 21) "int_result" [negative, array, UInt64.ofNat n] s
        = .ok (.gave o, { s' with memory := memory })
      ∧ ObjectOf memory o negative (keptLimbs limbs n)
      ∧ ∀ q, (∀ k, k < 16 + 4 * trimCount limbs n → o + UInt64.ofNat k ≠ q) → memory q = s'.memory q := by
  have hle := trimCount_le limbs n
  obtain ⟨memory, made, object, frame⟩ := bigNew_object outside (n - trimCount limbs n + extra) negative array o
    limbs _ s s' (by omega) small sign alloc (elements_kept _ _ _ _ elements kept) apart
  rw [show trimCount limbs n + (n - trimCount limbs n + extra) + 16 = n + extra + 16 from by omega] at made
  exact ⟨memory, (intResult_pass outside array negative limbs s n extra small elements hn range).2 o _ made,
    object, frame⟩

/-- `nat_from` is `nat_result` and then giving the array up: where either does not return neither does it,
and otherwise it gives what `nat_result` gave, in the state `lean_dec` leaves. -/
theorem natFrom_pass (outside : Outside) (fuel : Nat) (array count : UInt64) (s : State)
    (size : readBytes s.memory (array + 8) 8 = .ok count) :
    (∀ why, program.call outside (fuel + 2) "nat_result" [array, count] s = .error why →
      program.call outside (fuel + 4) "nat_from" [array] s = .error why) ∧
    ∀ value s1, program.call outside (fuel + 2) "nat_result" [array, count] s = .ok (.gave value, s1) →
      (∀ why, outside "lean_dec" [array] s1 = .error why →
        program.call outside (fuel + 4) "nat_from" [array] s = .error why) ∧
      ∀ unused after, outside "lean_dec" [array] s1 = .ok (unused, after) →
        program.call outside (fuel + 4) "nat_from" [array] s = .ok (.gave value, after) := by
  refine ⟨fun why run => ?_, fun value s1 run => ⟨fun why dec => ?_, fun unused after dec => ?_⟩⟩
  · have hl := runAll_of_fails program outside _ "nat_result" natResult _ s why find_natResult run
    simp [Program.call, find_natFrom, find_natResult, natFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, size]
    simp [Bind.bind, Except.bind, hl]
  · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "nat_result" natResult _ s _ _ find_natResult run
    simp [Program.call, find_natFrom, find_natResult, natFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, size]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl, dec]
  · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "nat_result" natResult _ s _ _ find_natResult run
    simp [Program.call, find_natFrom, find_natResult, natFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
      sizeOf, drop, size]
    simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl, dec]

/-- `nat_from` where the answer is 2^63 or more: it makes the object `nat_result` makes and then gives the
array up. If `lean_dec` returns, it gives back the object, in the state `lean_dec` leaves from one in which
the object is right. -/
theorem natFrom_object (outside : Outside) (array o : UInt64) (limbs : Runtime.Big.Limbs) (s s' : State)
    (extra : Nat) (small : limbs.size < 4294967296) (holds : ArrayOf s.memory array limbs)
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs limbs.size)] s = .ok (o, s'))
    (kept : ∀ j, j < 24 + 8 * limbs.size → s'.memory (array + UInt64.ofNat j) = s.memory (array + UInt64.ofNat j))
    (apart : ∀ k, k < 16 + 4 * trimCount limbs limbs.size → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∃ memory,
      ObjectOf memory o 0 (keptLimbs limbs limbs.size)
      ∧ (∀ q, (∀ k, k < 16 + 4 * trimCount limbs limbs.size → o + UInt64.ofNat k ≠ q) →
          memory q = s'.memory q)
      ∧ ∀ unused after, outside "lean_dec" [array] { s' with memory := memory } = .ok (unused, after) →
          program.call outside (limbs.size + extra + 24) "nat_from" [array] s = .ok (.gave o, after) := by
  obtain ⟨memory, run, object, frame⟩ := natResult_object outside array o limbs s s' extra small holds.2.2 big
    alloc kept apart
  exact ⟨memory, object, frame,
    ((natFrom_pass outside (limbs.size + extra + 20) array _ s holds.2.1).2 o _ run).2⟩

/-- The sign `int_from` reads off the element after the limbs: 0 if that element is zero, otherwise 1. -/
def topSign (limbs : Runtime.Big.Limbs) (n : Nat) : UInt64 := if limbs.getD n 0 = 0 then 0 else 1

theorem topSign_le (limbs : Runtime.Big.Limbs) (n : Nat) : topSign limbs n ≤ 1 := by
  unfold topSign
  split <;> decide

/-- The integer in an array the arithmetic returned is that sign on the number in the limbs below it. -/
theorem signedValue_topSign (limbs : Runtime.Big.Limbs) (n : Nat) (size : limbs.size = n + 1) :
    Runtime.Big.signedValue limbs = withSign (topSign limbs n) (Runtime.Big.lower limbs n) := by
  have pop : Runtime.Big.value limbs.pop = Runtime.Big.lower limbs n := by
    rw [value_pop_lower, size, Nat.add_sub_cancel]
  by_cases top : limbs.getD n 0 = 0 <;>
    simp [Runtime.Big.signedValue, Runtime.Big.intOf, size, top, pop, withSign, topSign]

/-- `int_from` is `int_result`, on the sign after the limbs and the limbs, and then giving the array up:
where either does not return neither does it, and otherwise it gives what `int_result` gave, in the state
`lean_dec` leaves. -/
theorem intFrom_pass (outside : Outside) (fuel n : Nat) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (holds : ArrayOf s.memory array limbs) (size : limbs.size = n + 1) (small : limbs.size < 4294967296) :
    (∀ why, program.call outside (fuel + 2) "int_result" [topSign limbs n, array, UInt64.ofNat n] s = .error why →
      program.call outside (fuel + 6) "int_from" [array] s = .error why) ∧
    ∀ value s1, program.call outside (fuel + 2) "int_result" [topSign limbs n, array, UInt64.ofNat n] s
        = .ok (.gave value, s1) →
      (∀ why, outside "lean_dec" [array] s1 = .error why →
        program.call outside (fuel + 6) "int_from" [array] s = .error why) ∧
      ∀ unused after, outside "lean_dec" [array] s1 = .ok (unused, after) →
        program.call outside (fuel + 6) "int_from" [array] s = .ok (.gave value, after) := by
  have hsize := holds.2.1
  rw [size] at hsize
  have read := holds.2.2 n (by omega)
  rw [← below_count] at read
  generalize hc : UInt64.ofNat (n + 1) = c at hsize read
  have cpos : c ≠ 0 := by
    intro z
    have := congrArg UInt64.toNat (hc.trans z)
    simp only [UInt64.toNat_ofNat', show (0 : UInt64).toNat = 0 from rfl] at this
    omega
  have cless : UInt64.ofNat n = c - 1 := by
    rw [← hc]
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_sub, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl]
    omega
  rw [cless]
  have element : limbs.getD n 0 = limbs[n]'(by omega) := by simp [Array.getD, show n < limbs.size by omega]
  by_cases top : limbs[n]'(by omega) = 0
  · have ts : topSign limbs n = 0 := by simp [topSign, element, top]
    have hz : (limbs[n]'(by omega)).toUInt64 = 0 := by rw [top]; rfl
    rw [ts]
    refine ⟨fun why run => ?_, fun value s1 run => ⟨fun why dec => ?_, fun unused after dec => ?_⟩⟩
    · have hl := runAll_of_fails program outside _ "int_result" intResult _ s why find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hz, hl,
        show boxed 0 >>> 1 = 0 from by decide]
    · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hz, hl, dec,
        show boxed 0 >>> 1 = 0 from by decide]
    · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hz, hl, dec,
        show boxed 0 >>> 1 = 0 from by decide]
  · have ts : topSign limbs n = 1 := by simp [topSign, element, top]
    have nz := limb_nonzero _ top
    rw [ts]
    refine ⟨fun why run => ?_, fun value s1 run => ⟨fun why dec => ?_, fun unused after dec => ?_⟩⟩
    · have hl := runAll_of_fails program outside _ "int_result" intResult _ s why find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hl,
        unbox_boxed, nz]
    · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hl, dec,
        unbox_boxed, nz]
    · obtain ⟨l, hl⟩ := runAll_of_call program outside _ "int_result" intResult _ s _ _ find_intResult run
      simp [Program.call, find_intFrom, find_intResult, intFrom, runAll, Stmt.run, Expr.run, Op.run, bind, put,
        sizeOf, drop, limbAt, unbox, Expr.eq, Expr.ne, Expr.shr, hsize]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, cpos, read, hl, dec,
        unbox_boxed, nz]

/-- `int_from` where the answer is outside the range a tagged word holds: it makes the object `int_result`
makes, holding the sign and the limbs of the integer in the array (`signedValue`), and then gives the array
up. If `lean_dec` returns, it gives back the object, in the state `lean_dec` leaves from one in which the
object is right. -/
theorem intFrom_object (outside : Outside) (array o : UInt64) (limbs : Runtime.Big.Limbs) (s s' : State)
    (n extra : Nat) (small : limbs.size < 4294967296) (holds : ArrayOf s.memory array limbs)
    (size : limbs.size = n + 1)
    (range : Runtime.Big.signedValue limbs < -2147483648 ∨ 2147483648 ≤ Runtime.Big.signedValue limbs)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs n)] s = .ok (o, s'))
    (kept : ∀ j, j < 24 + 8 * limbs.size → s'.memory (array + UInt64.ofNat j) = s.memory (array + UInt64.ofNat j))
    (apart : ∀ k, k < 16 + 4 * trimCount limbs n → ∀ j, j < 24 + 8 * limbs.size →
      o + UInt64.ofNat k ≠ array + UInt64.ofNat j) :
    ∃ memory negative,
      ObjectOf memory o negative (keptLimbs limbs n)
      ∧ withSign negative (Runtime.Big.value (keptLimbs limbs n)) = Runtime.Big.signedValue limbs
      ∧ (∀ q, (∀ k, k < 16 + 4 * trimCount limbs n → o + UInt64.ofNat k ≠ q) → memory q = s'.memory q)
      ∧ ∀ unused after, outside "lean_dec" [array] { s' with memory := memory } = .ok (unused, after) →
          program.call outside (n + extra + 25) "int_from" [array] s = .ok (.gave o, after) := by
  have sv := signedValue_topSign limbs n size
  obtain ⟨memory, run, object, frame⟩ := intResult_object outside array (topSign limbs n) o limbs s s' n extra
    small holds.2.2 (by omega) (topSign_le limbs n) (by rw [← sv]; exact range) alloc kept apart
  exact ⟨memory, topSign limbs n, object, by rw [keptLimbs_value limbs n (by omega), sv], frame,
    ((intFrom_pass outside (n + extra + 19) n array limbs s holds size small).2 o _ run).2⟩

/-! ## More fuel

A run that finished finishes the same with more fuel. So a statement about a call that returned need not say
how much fuel it was given. -/

/-- One more unit of fuel changes nothing that finished, for a statement and for a run of them. -/
theorem more_fuel (p : Program) (outside : Outside) : ∀ fuel : Nat,
    (∀ st s locals r, Stmt.run p outside fuel st s locals = .ok r →
      Stmt.run p outside (fuel + 1) st s locals = .ok r) ∧
    (∀ sts s locals r, runAll p outside fuel sts s locals = .ok r →
      runAll p outside (fuel + 1) sts s locals = .ok r) := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨fun st s locals r h => ?_, fun sts s locals r h => ?_⟩
    · simp [Stmt.run] at h
    · simp [runAll] at h
  | succ fuel ih =>
    obtain ⟨ihs, iha⟩ := ih
    refine ⟨fun st s locals r h => ?_, fun sts s locals r h => ?_⟩
    · cases st with
      | branch condition yes no =>
        rw [Stmt.run] at h ⊢
        cases c : condition.run s locals with
        | error e => rw [c] at h; simp [Bind.bind, Except.bind] at h
        | ok v =>
          rw [c] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          by_cases z : (v != 0) = true
          · simp only [z] at h ⊢; exact iha _ _ _ _ h
          · simp only [z] at h ⊢; exact iha _ _ _ _ h
      | loop condition body =>
        rw [Stmt.run] at h ⊢
        cases c : condition.run s locals with
        | error e => rw [c] at h; simp [Bind.bind, Except.bind] at h
        | ok v =>
          rw [c] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          by_cases z : (v == 0) = true
          · simp only [z] at h ⊢; exact h
          · simp only [z] at h ⊢
            cases b : runAll p outside fuel body s locals with
            | error e => rw [b] at h; first | cases h | simp [Bind.bind, Except.bind] at h
            | ok r1 =>
              rw [b] at h
              rw [iha _ _ _ _ b]
              obtain ⟨e1, s1, l1⟩ := r1
              cases e1 with
              | on => exact ihs _ _ _ _ h
              | gave value => exact h
              | stopped why => exact h
      | call result function arguments =>
        simp only [Stmt.run] at h ⊢
        cases a : arguments.mapM (fun x => x.run s locals) with
        | error e => rw [a] at h; simp [Bind.bind, Except.bind] at h
        | ok values =>
          rw [a] at h
          simp only [Bind.bind, Except.bind] at h ⊢
          cases f : p.functions.find? (fun x => x.name == function) with
          | none => rw [f] at h; simp at h
          | some fn =>
            rw [f] at h
            simp only at h ⊢
            cases b : runAll p outside fuel fn.body s (bind (fun _ => none) fn.parameters values) with
            | error e => rw [b] at h; first | cases h | simp [Bind.bind, Except.bind] at h
            | ok r1 =>
              rw [b] at h
              rw [iha _ _ _ _ b]
              exact h
      | _ => rw [Stmt.run] at h ⊢; exact h
    · cases sts with
      | nil => simp only [runAll] at h ⊢; exact h
      | cons st rest =>
        rw [runAll] at h ⊢
        cases b : Stmt.run p outside fuel st s locals with
        | error e => rw [b] at h; first | cases h | simp [Bind.bind, Except.bind] at h
        | ok r1 =>
          rw [b] at h
          rw [ihs _ _ _ _ b]
          obtain ⟨e1, s1, l1⟩ := r1
          cases e1 with
          | on => exact iha _ _ _ _ h
          | gave value => exact h
          | stopped why => exact h

/-- Nor does any amount more. -/
theorem runAll_more (p : Program) (outside : Outside) (fuel more : Nat) (sts : List Stmt) (s : State)
    (locals : Locals) (r : Ending × State × Locals) (h : runAll p outside fuel sts s locals = .ok r) :
    runAll p outside (fuel + more) sts s locals = .ok r := by
  induction more with
  | zero => exact h
  | succ n ih => exact (more_fuel p outside _).2 _ _ _ _ ih

/-- A call that returned returns the same with more fuel. -/
theorem call_more (p : Program) (outside : Outside) (fuel more : Nat) (function : String)
    (arguments : List UInt64) (s : State) (r : Ending × State)
    (h : p.call outside fuel function arguments s = .ok r) :
    p.call outside (fuel + more) function arguments s = .ok r := by
  unfold Program.call at h ⊢
  cases f : p.functions.find? (fun x => x.name == function) with
  | none => rw [f] at h; cases h
  | some fn =>
    rw [f] at h
    dsimp only at h ⊢
    cases b : runAll p outside fuel fn.body s (bind (fun _ => none) fn.parameters arguments) with
    | error e => rw [b] at h; cases h
    | ok r1 =>
      rw [b] at h
      rw [runAll_more p outside fuel more _ _ _ _ b]
      exact h

/-! ## Where the allocator does not return

`lean_alloc_object` does not return when there is no memory left. Then the function that asked does not
return either, and so on up: none of them carries on with an address it was not given. -/

theorem arrayNew_fails (outside : Outside) (fuel : Nat) (count : UInt64) (s : State) (why : String)
    (alloc : outside "lean_alloc_object" [24 + count * 8] s = .error why) :
    program.call outside (fuel + 10) "array_new" [count] s = .error why := by
  simp [Program.call, find_arrayNew, arrayNew, runAll, Stmt.run, Expr.run, Op.run, bind, put, header, alloc]
  rfl

theorem limbsOfWord_fails (outside : Outside) (fuel : Nat) (value : UInt64) (s : State) (why : String)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs value).size)] s = .error why) :
    program.call outside (fuel + 20) "limbs_of_word" [value] s = .error why := by
  by_cases hz : value = 0
  · subst hz
    have alloc' : outside "lean_alloc_object" [24] s = .error why := alloc
    simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run, Op.run,
      bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc']
    rfl
  · by_cases hs : value ≤ 4294967295
    · have w : wordLimbs value = #[value.toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc
      have alloc' : outside "lean_alloc_object" [32] s = .error why := alloc
      simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run,
        Op.run, bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc', hz,
        hs]
      rfl
    · have hl : (4294967295 : UInt64) < value := by simpa [UInt64.not_le] using hs
      have w : wordLimbs value = #[value.toUInt32, (value >>> 32).toUInt32] := by simp [wordLimbs, hz, hs]
      rw [w] at alloc
      have alloc' : outside "lean_alloc_object" [40] s = .error why := alloc
      simp [Program.call, find_limbsOfWord, find_arrayNew, limbsOfWord, arrayNew, runAll, Stmt.run, Expr.run,
        Op.run, bind, put, header, low32, box, Expr.ne, Expr.lt, Expr.and, Expr.or, Expr.shl, Expr.shr, alloc', hz,
        hs]
      rfl

theorem natLimbs_word_fails (outside : Outside) (fuel : Nat) (o : UInt64) (s : State) (why : String)
    (tagged : o &&& 1 ≠ 0)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * (wordLimbs (o >>> 1)).size)] s = .error why) :
    program.call outside (fuel + 24) "nat_limbs" [o] s = .error why := by
  have hl := runAll_of_fails program outside (fuel + 20) "limbs_of_word" limbsOfWord [o >>> 1] s why
    find_limbsOfWord (limbsOfWord_fails outside fuel (o >>> 1) s why alloc)
  simp [Program.call, find_natLimbs, find_limbsOfWord, natLimbs, runAll, Stmt.run, Expr.run, Op.run, bind, put,
    isWord, unbox, Expr.ne, Expr.and, Expr.shr, tagged, hl]
  simp [Bind.bind, Except.bind]

theorem limbsOfObject_fails (outside : Outside) (extra n : Nat) (o : UInt64) (s : State) (why : String)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * n)] s = .error why) :
    program.call outside (n + extra + 14) "limbs_of_object" [o, UInt64.ofNat n] s = .error why := by
  have room : (24 : UInt64) + UInt64.ofNat n * 8 = UInt64.ofNat (24 + 8 * n) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (24 : UInt64).toNat = 24 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    omega
  rw [← room] at alloc
  have hl0 : runAll program outside (n + extra + 12) arrayNew.body s
      (bind (fun _ => none) arrayNew.parameters [UInt64.ofNat n]) = .error why :=
    runAll_of_fails program outside _ "array_new" arrayNew _ s why find_arrayNew
      (arrayNew_fails outside (n + extra + 2) (UInt64.ofNat n) s why alloc)
  have st1 : Stmt.run program outside (n + extra + 13) (.call (some "array") "array_new" ["count"]) s
      (bind (fun _ => none) ["o", "count"] [o, UInt64.ofNat n]) = .error why := by
    simp [Stmt.run, find_arrayNew, Expr.run, bind, put, hl0]
    rfl
  exact call_fails program outside _ "limbs_of_object" limbsOfObject _ s why find_limbsOfObject
    (runAll_fails _ _ _ _ _ _ _ _ st1)

theorem bigNew_fails (outside : Outside) (extra count : Nat) (negative array : UInt64) (s : State) (why : String)
    (small : count < 4294967296)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * count)] s = .error why) :
    program.call outside (count + extra + 16) "big_new" [negative, array, UInt64.ofNat count] s = .error why := by
  have room : (16 : UInt64) + UInt64.ofNat count * 4 = UInt64.ofNat (16 + 4 * count) := by
    apply UInt64.toNat_inj.mp
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', show (16 : UInt64).toNat = 16 from rfl,
      show (4 : UInt64).toNat = 4 from rfl]
    omega
  rw [← room] at alloc
  have fits : UInt64.ofNat count ≤ 4294967295 := by
    rw [UInt64.le_iff_toNat_le]
    simp only [UInt64.toNat_ofNat', show (4294967295 : UInt64).toNat = 4294967295 from rfl]
    omega
  generalize UInt64.ofNat count = cw at alloc fits
  generalize hlocals : bind (fun _ => none) ["negative", "array", "count"] [negative, array, cw] = locals
  have lcount : locals "count" = some cw := by rw [← hlocals]; simp [bind, put]
  have st0 : Stmt.run program outside (count + extra + 15) (.branch (Expr.lt low32 "count") [outOfMemory] []) s
      locals = .ok (.on, s, locals) := by
    simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, low32, lcount, fits]
    rfl
  have st1 : Stmt.run program outside (count + extra + 14)
      (.callOther (some "o") "lean_alloc_object" [16 + "count" * 4]) s locals = .error why := by
    simp [Stmt.run, Expr.run, Op.run, lcount, alloc]
    rfl
  refine call_fails program outside _ "big_new" bigNew _ s why find_bigNew ?_
  show runAll program outside (count + extra + 15 + 1) [.branch (Expr.lt low32 "count") [outOfMemory] [],
    .callOther (some "o") "lean_alloc_object" [16 + "count" * 4],
    .store "o" (header numberKind),
    .storePart 4 ("o" + 8) "negative",
    .storePart 4 ("o" + 12) "count",
    .set "i" 0,
    .loop (Expr.lt "i" "count")
      [.storePart 4 ("o" + 16 + "i" * 4) (limbAt "array" "i"), .set "i" ("i" + 1)],
    .give "o"] s (bind (fun _ => none) ["negative", "array", "count"] [negative, array, cw]) = _
  rw [hlocals]
  exact (runAll_on _ _ _ _ _ _ _ _ _ st0).trans (runAll_fails _ _ (count + extra + 14) _ _ _ _ _ st1)

theorem natResult_fails (outside : Outside) (array : UInt64) (limbs : Runtime.Big.Limbs) (s : State)
    (extra : Nat) (why : String) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (big : 9223372036854775808 ≤ Runtime.Big.value limbs)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs limbs.size)] s = .error why) :
    program.call outside (limbs.size + extra + 22) "nat_result" [array, UInt64.ofNat limbs.size] s
      = .error why := by
  have hle := trimCount_le limbs limbs.size
  have fails := bigNew_fails outside (limbs.size - trimCount limbs limbs.size + extra) _ 0 array s why
    (by omega) alloc
  rw [show trimCount limbs limbs.size + (limbs.size - trimCount limbs limbs.size + extra) + 16
    = limbs.size + extra + 16 from by omega] at fails
  exact (natResult_pass outside array limbs s extra small elements big).1 why fails

/-! ## An operation as a whole

From the words compiled Lean hands in to the word it gets back. What the program calls outside itself is
now assumed as a whole rather than call by call: `Allocator` says what `lean_alloc_object` and `lean_dec`
do, `Computes` and `Compares` what a call into the compiled arithmetic does. Each statement then reads: if
the operation returns, it returns the right number as compiled Lean holds it, and every object that was
there before is there and as it was. Nothing is said of a call that does not return. -/

/-- What is assumed of the allocator, for an operation as a whole. `good` says the allocator's own account
of a state is in order. `owns t p q` says that in state `t` byte `q` is part of the object handed out at
`p` and not given back. -/
structure Allocator (outside : Outside) where
  good : State → Prop
  owns : State → UInt64 → UInt64 → Prop
  /-- Writing inside objects that have been handed out does not disturb the allocator. -/
  written : ∀ (t : State) (memory : UInt64 → Option UInt8), good t →
    (∀ q, (∀ p, ¬ owns t p q) → memory q = t.memory q) →
    good { t with memory := memory } ∧ owns { t with memory := memory } = owns t
  /-- Room that is handed out is at an even address, was nobody's, and is the new object's; every object
  there already is still there and as it was. -/
  alloc : ∀ (size : UInt64) (t : State) (p : UInt64) (t' : State), good t →
    outside "lean_alloc_object" [size] t = .ok (p, t') →
    good t' ∧ p &&& 1 = 0 ∧
    (∀ p0 q, owns t p0 q → p0 ≠ p ∧ owns t' p0 q ∧ t'.memory q = t.memory q) ∧
    ∀ k, k < size.toNat → owns t' p (p + UInt64.ofNat k) ∧ ∀ p0, ¬ owns t p0 (p + UInt64.ofNat k)
  /-- Giving up an array of limbs leaves every other object there and as it was. -/
  dec : ∀ (array : UInt64) (limbs : Runtime.Big.Limbs) (t : State) (unused : UInt64) (t' : State), good t →
    ArrayOf t.memory array limbs →
    (∀ k, k < 24 + 8 * limbs.size → owns t array (array + UInt64.ofNat k)) →
    outside "lean_dec" [array] t = .ok (unused, t') →
    good t' ∧ ∀ p0 q, owns t p0 q → p0 ≠ array → owns t' p0 q ∧ t'.memory q = t.memory q

/-- What is assumed of a call into the compiled arithmetic: that it does to arrays in memory what the Lean
function does to its arguments. Handed two different arrays of limbs, each an object of its own, it returns
an array holding the function's answer, which is an object of its own and none of those that were there
besides the two; and it leaves every object but the two there and as it was. The two are the arithmetic's
to use or to give up. -/
def Computes {outside : Outside} (heap : Allocator outside) (name : String)
    (f : Runtime.Big.Limbs → Runtime.Big.Limbs → Runtime.Big.Limbs) : Prop :=
  ∀ (a b : UInt64) (la lb : Runtime.Big.Limbs) (t : State) (array : UInt64) (t' : State), heap.good t →
    ArrayOf t.memory a la → ArrayOf t.memory b lb →
    (∀ k, k < 24 + 8 * la.size → heap.owns t a (a + UInt64.ofNat k)) →
    (∀ k, k < 24 + 8 * lb.size → heap.owns t b (b + UInt64.ofNat k)) → a ≠ b →
    outside name [a, b] t = .ok (array, t') →
    heap.good t' ∧ ArrayOf t'.memory array (f la lb) ∧
    (∀ k, k < 24 + 8 * (f la lb).size → heap.owns t' array (array + UInt64.ofNat k)) ∧
    ∀ p0 q, heap.owns t p0 q → p0 ≠ a → p0 ≠ b →
      p0 ≠ array ∧ heap.owns t' p0 q ∧ t'.memory q = t.memory q

/-- A natural number as compiled Lean holds it: below 2^63 a tagged word, twice the number and one; from
there up an object of its own, whose limbs are the number's and whose top limb is not zero. -/
def NatHeld {outside : Outside} (heap : Allocator outside) (t : State) (o : UInt64) (n : Nat) : Prop :=
  (n < 9223372036854775808 ∧ o = UInt64.ofNat (2 * n + 1)) ∨
  (9223372036854775808 ≤ n ∧ o &&& 1 = 0 ∧ ∃ limbs : Runtime.Big.Limbs,
    ObjectOf t.memory o 0 limbs ∧ limbs.size < 4294967296 ∧ Runtime.Big.Trimmed limbs ∧
    Runtime.Big.value limbs = n ∧ ∀ j, j < 16 + 4 * limbs.size → heap.owns t o (o + UInt64.ofNat j))

/-- An array whose bytes are as they were still holds what it held. -/
theorem array_kept (memory memory' : UInt64 → Option UInt8) (array : UInt64) (limbs : Runtime.Big.Limbs)
    (holds : ArrayOf memory array limbs)
    (kept : ∀ j, j < 24 + 8 * limbs.size → memory' (array + UInt64.ofNat j) = memory (array + UInt64.ofNat j)) :
    ArrayOf memory' array limbs := by
  obtain ⟨header, size, elements⟩ := holds
  refine ⟨?_, ?_, elements_kept memory memory' array limbs elements kept⟩
  · exact (readBytes_congr _ _ _ _ (fun i hi => kept i (by omega))).trans header
  · exact (readBytes_congr _ _ (array + UInt64.ofNat 8) _ (fun i hi => by
      rw [offset_add]; exact kept _ (by omega))).trans size

/-- A number that is held stays held while every object that was there is there and as it was. -/
theorem natHeld_kept {outside : Outside} (heap : Allocator outside) (t t' : State) (o : UInt64) (n : Nat)
    (held : NatHeld heap t o n)
    (kept : ∀ p0 q, heap.owns t p0 q → heap.owns t' p0 q ∧ t'.memory q = t.memory q) :
    NatHeld heap t' o n := by
  rcases held with word | ⟨big, pointer, limbs, holds, small, nozero, value, owned⟩
  · exact Or.inl word
  · exact Or.inr ⟨big, pointer, limbs,
      object_kept t.memory t'.memory o 0 limbs holds (fun j hj => (kept o _ (owned j hj)).2), small, nozero, value,
      fun j hj => (kept o _ (owned j hj)).1⟩

theorem tagged_word (n : Nat) : UInt64.ofNat (2 * n + 1) &&& 1 ≠ 0 := by
  intro e
  have := congrArg UInt64.toNat e
  rw [UInt64.toNat_and, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl, Nat.and_one_is_mod] at this
  have z : (0 : UInt64).toNat = 0 := rfl
  omega

theorem half_word (n : Nat) (h : n < 9223372036854775808) : UInt64.ofNat (2 * n + 1) >>> 1 = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_shiftRight, UInt64.toNat_ofNat', show (1 : UInt64).toNat = 1 from rfl,
    Nat.shiftRight_eq_div_pow, show 1 % 64 = 1 from rfl, Nat.pow_one]
  omega

theorem wordLimbs_size (value : UInt64) : (wordLimbs value).size ≤ 2 := by
  unfold wordLimbs
  split
  · simp
  · split <;> simp

/-- What the allocator's promises come to for room this program asked for and then wrote in. -/
theorem room_made {outside : Outside} (heap : Allocator outside) (bytes : Nat) (s s' : State) (p : UInt64)
    (memory : UInt64 → Option UInt8) (good : heap.good s) (fits : bytes < 18446744073709551616)
    (alloc : outside "lean_alloc_object" [UInt64.ofNat bytes] s = .ok (p, s'))
    (frame : ∀ q, (∀ k, k < bytes → p + UInt64.ofNat k ≠ q) → memory q = s'.memory q) :
    heap.good { s' with memory := memory } ∧
    (∀ k, k < bytes → heap.owns { s' with memory := memory } p (p + UInt64.ofNat k)) ∧
    ∀ p0 q, heap.owns s p0 q →
      p0 ≠ p ∧ heap.owns { s' with memory := memory } p0 q ∧ memory q = s.memory q := by
  obtain ⟨good', -, others, room⟩ := heap.alloc _ s p s' good alloc
  have size : (UInt64.ofNat bytes).toNat = bytes := by
    simp only [UInt64.toNat_ofNat']
    omega
  rw [size] at room
  obtain ⟨good'', same⟩ := heap.written s' memory good'
    (fun q nobody => frame q (fun k hk e => nobody p (e ▸ (room k hk).1)))
  refine ⟨good'', fun k hk => by rw [same]; exact (room k hk).1, fun p0 q own => ?_⟩
  obtain ⟨ne, own', mem⟩ := others p0 q own
  exact ⟨ne, by rw [same]; exact own', (frame q (fun k hk e => (room k hk).2 p0 (e ▸ own))).trans mem⟩

/-- `nat_limbs` on a natural number as compiled Lean holds it: if it returns, it gives an array, an object
of its own, holding limbs of that number with no zero limb on top; and every object that was there is
there and as it was. -/
theorem natLimbs_held {outside : Outside} (heap : Allocator outside) (fuel : Nat) (o : UInt64) (n : Nat)
    (s after : State) (ending : Ending) (good : heap.good s) (held : NatHeld heap s o n)
    (ran : program.call outside fuel "nat_limbs" [o] s = .ok (ending, after)) :
    ∃ array limbs, ending = .gave array ∧ heap.good after ∧ ArrayOf after.memory array limbs ∧
      limbs.size < 4294967296 ∧ Runtime.Big.Trimmed limbs ∧ Runtime.Big.value limbs = n ∧
      (∀ k, k < 24 + 8 * limbs.size → heap.owns after array (array + UInt64.ofNat k)) ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ array ∧ heap.owns after p0 q ∧ after.memory q = s.memory q := by
  rcases held with ⟨lt, rfl⟩ | ⟨big, pointer, limbs, holds, small, nozero, value, owned⟩
  · have tagged := tagged_word n
    have half := half_word n lt
    have two := wordLimbs_size (UInt64.ofNat (2 * n + 1) >>> 1)
    have lifted := call_more program outside fuel 24 "nat_limbs" [UInt64.ofNat (2 * n + 1)] s _ ran
    cases a : outside "lean_alloc_object"
        [UInt64.ofNat (24 + 8 * (wordLimbs (UInt64.ofNat (2 * n + 1) >>> 1)).size)] s with
    | error why =>
      rw [natLimbs_word_fails outside fuel _ s why tagged a] at lifted
      cases lifted
    | ok r =>
      obtain ⟨array, s'⟩ := r
      obtain ⟨memory, run, holds, frame⟩ := natLimbs_word outside fuel _ array s s' tagged a
      rw [run] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', room, others⟩ := room_made heap _ s s' array memory good (by omega) a frame
      refine ⟨array, _, rfl, good', holds, by omega, wordLimbs_trimmed _, ?_, room, others⟩
      rw [wordLimbs_value, half, UInt64.toNat_ofNat']
      omega
  · have big' : 9223372036854775808 ≤ Runtime.Big.value limbs := by rw [value]; exact big
    have lifted := call_more program outside fuel (limbs.size + 20) "nat_limbs" [o] s _ ran
    rw [show fuel + (limbs.size + 20) = limbs.size + fuel + 20 from by omega] at lifted
    have pass := natLimbs_object_pass outside fuel o limbs s pointer holds small nozero big'
    cases a : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * limbs.size)] s with
    | error why =>
      rw [pass.1 why (limbsOfObject_fails outside fuel limbs.size o s why a)] at lifted
      cases lifted
    | ok r =>
      obtain ⟨array, s'⟩ := r
      obtain ⟨-, -, others, room⟩ := heap.alloc _ s array s' good a
      have size : (UInt64.ofNat (24 + 8 * limbs.size)).toNat = 24 + 8 * limbs.size := by
        simp only [UInt64.toNat_ofNat']
        omega
      rw [size] at room
      obtain ⟨memory, run, holds', frame⟩ := limbsOfObject_array outside fuel o array limbs s s' small a
        (object_kept s.memory s'.memory o 0 limbs holds (fun j hj => (others o _ (owned j hj)).2.2)).2.2.2
        (fun k hk j hj e => (room k hk).2 o (e ▸ owned j hj))
      rw [pass.2 array _ run] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', room', others'⟩ := room_made heap _ s s' array memory good (by omega) a frame
      exact ⟨array, limbs, rfl, good', holds', small, nozero, value, room', others'⟩

/-- `nat_from` on an array of limbs that is an object of its own: if it returns, it gives the number in the
array as compiled Lean holds it, and every object that was there but the array is there and as it was. -/
theorem natFrom_held {outside : Outside} (heap : Allocator outside) (fuel : Nat) (array : UInt64)
    (limbs : Runtime.Big.Limbs) (s after : State) (ending : Ending) (good : heap.good s)
    (holds : ArrayOf s.memory array limbs) (small : limbs.size < 4294967296)
    (owned : ∀ k, k < 24 + 8 * limbs.size → heap.owns s array (array + UInt64.ofNat k))
    (ran : program.call outside fuel "nat_from" [array] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧
      NatHeld heap after result (Runtime.Big.value limbs) ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ array → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  by_cases fits : Runtime.Big.value limbs < 9223372036854775808
  · have run := natResult_word outside array limbs s fuel (by omega) holds fits
    have pass := (natFrom_pass outside (limbs.size + fuel + 8) array _ s holds.2.1).2 _ _ run
    have lifted := call_more program outside fuel (limbs.size + 12) "nat_from" [array] s _ ran
    rw [show fuel + (limbs.size + 12) = limbs.size + fuel + 8 + 4 from by omega] at lifted
    cases d : outside "lean_dec" [array] s with
    | error why =>
      rw [pass.1 why d] at lifted
      cases lifted
    | ok r =>
      obtain ⟨unused, after'⟩ := r
      rw [pass.2 unused after' d] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', others⟩ := heap.dec array limbs s unused after' good holds owned d
      exact ⟨_, rfl, good', Or.inl ⟨fits, rfl⟩, others⟩
  · have big : 9223372036854775808 ≤ Runtime.Big.value limbs := by omega
    have hle := trimCount_le limbs limbs.size
    have lifted := call_more program outside fuel (limbs.size + 24) "nat_from" [array] s _ ran
    rw [show fuel + (limbs.size + 24) = limbs.size + fuel + 20 + 4 from by omega] at lifted
    have pass := natFrom_pass outside (limbs.size + fuel + 20) array _ s holds.2.1
    cases a : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs limbs.size)] s with
    | error why =>
      rw [pass.1 why (natResult_fails outside array limbs s fuel why small holds.2.2 big a)] at lifted
      cases lifted
    | ok r =>
      obtain ⟨o, s'⟩ := r
      obtain ⟨-, even, others, room⟩ := heap.alloc _ s o s' good a
      have size : (UInt64.ofNat (16 + 4 * trimCount limbs limbs.size)).toNat
          = 16 + 4 * trimCount limbs limbs.size := by
        simp only [UInt64.toNat_ofNat']
        omega
      rw [size] at room
      obtain ⟨memory, run, object, frame⟩ := natResult_object outside array o limbs s s' fuel small holds.2.2 big a
        (fun j hj => (others array _ (owned j hj)).2.2)
        (fun k hk j hj e => (room k hk).2 array (e ▸ owned j hj))
      obtain ⟨good', room', others'⟩ := room_made heap _ s s' o memory good (by omega) a frame
      have pass' := pass.2 o _ run
      cases d : outside "lean_dec" [array] { s' with memory := memory } with
      | error why =>
        rw [pass'.1 why d] at lifted
        cases lifted
      | ok r =>
        obtain ⟨unused, after'⟩ := r
        rw [pass'.2 unused after' d] at lifted
        injection lifted with same
        injection same with e1 e2
        subst e1 e2
        obtain ⟨good'', others''⟩ := heap.dec array limbs { s' with memory := memory } unused after' good'
          (array_kept s.memory memory array limbs holds (fun j hj => (others' array _ (owned j hj)).2.2))
          (fun k hk => (others' array _ (owned k hk)).2.1) d
        have apart : o ≠ array := fun e => (others' array _ (owned 0 (by omega))).1 e.symm
        have ksize := keptLimbs_size limbs limbs.size (Nat.le_refl _)
        refine ⟨o, rfl, good'', Or.inr ⟨?_, even, keptLimbs limbs limbs.size, ?_, by omega,
          keptLimbs_trimmed limbs limbs.size (Nat.le_refl _), ?_, ?_⟩, fun p0 q own ne => ?_⟩
        · exact big
        · exact object_kept memory after'.memory o 0 _ object
            (fun j hj => (others'' o _ (room' j (by omega)) apart).2)
        · rw [keptLimbs_value limbs limbs.size (Nat.le_refl _), Runtime.Big.lower_size]
        · exact fun j hj => (others'' o _ (room' j (by omega)) apart).1
        · obtain ⟨-, own', mem⟩ := others' p0 q own
          obtain ⟨own'', mem'⟩ := others'' p0 q own' ne
          exact ⟨own'', mem'.trans mem⟩

/-- A call of a function of one argument, as a statement. -/
theorem call_stmt (p : Program) (outside : Outside) (fuel : Nat) (name function argument : String) (f : Function)
    (value : UInt64) (s : State) (locals : Locals)
    (found : p.functions.find? (fun f => f.name == function) = some f) (arg : locals argument = some value) :
    (∀ why, p.call outside fuel function [value] s = .error why →
      Stmt.run p outside (fuel + 1) (.call (some name) function [.var argument]) s locals = .error why) ∧
    ∀ v after, p.call outside fuel function [value] s = .ok (.gave v, after) →
      Stmt.run p outside (fuel + 1) (.call (some name) function [.var argument]) s locals
        = .ok (.on, after, put locals name (some v)) := by
  refine ⟨fun why h => ?_, fun v after h => ?_⟩
  · have body := runAll_of_fails p outside fuel function f _ s why found h
    simp [Stmt.run, found, Expr.run, arg, body]
    rfl
  · obtain ⟨l, body⟩ := runAll_of_call p outside fuel function f _ s _ _ found h
    simp [Stmt.run, found, Expr.run, arg, body]
    rfl

/-- An operation on two natural numbers, as a whole. -/
theorem natOperation_held {outside : Outside} (heap : Allocator outside) (name arithmetic about : String)
    (f : Runtime.Big.Limbs → Runtime.Big.Limbs → Runtime.Big.Limbs) (g : Nat → Nat → Nat)
    (found : program.functions.find? (fun f => f.name == name) = some (natOperation name arithmetic about))
    (computes : Computes heap arithmetic f)
    (right : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b →
      Runtime.Big.value (f a b) = g (Runtime.Big.value a) (Runtime.Big.value b))
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (f a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel name [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (g x y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  obtain ⟨locals, ran⟩ := runAll_of_call program outside fuel name _ [a1, a2] s after ending found ran
  have ran := runAll_more program outside fuel 6 _ _ _ _ ran
  generalize hl0 : bind (fun _ => none) (natOperation name arithmetic about).parameters [a1, a2] = l0 at ran
  have l0a1 : l0 "a1" = some a1 := by rw [← hl0]; simp [natOperation, bind, put]
  have l0a2 : l0 "a2" = some a2 := by rw [← hl0]; simp [natOperation, bind, put]
  change runAll program outside (fuel + 5 + 1) [.call (some "a") "nat_limbs" [.var "a1"],
    .call (some "b") "nat_limbs" [.var "a2"], .callOther (some "array") arithmetic [.var "a", .var "b"],
    .call (some "result") "nat_from" [.var "array"], .give (.var "result")] s l0 = _ at ran
  have step1 := call_stmt program outside (fuel + 4) "a" "nat_limbs" "a1" natLimbs a1 s l0 find_natLimbs l0a1
  cases h1 : program.call outside (fuel + 4) "nat_limbs" [a1] s with
  | error why =>
    rw [runAll_fails _ _ _ _ _ _ _ _ (step1.1 why h1)] at ran
    cases ran
  | ok r1 =>
    obtain ⟨e1, s1⟩ := r1
    obtain ⟨a, la, rfl, good1, arr1, -, trim1, val1, own1, kept1⟩ :=
      natLimbs_held heap _ a1 x s s1 e1 good first h1
    rw [runAll_on _ _ _ _ _ _ _ _ _ (step1.2 a s1 h1)] at ran
    have second1 := natHeld_kept heap s s1 a2 y second (fun p0 q own => (kept1 p0 q own).2)
    have step2 := call_stmt program outside (fuel + 3) "b" "nat_limbs" "a2" natLimbs a2 s1 (put l0 "a" (some a))
      find_natLimbs (by simp [put, l0a2])
    cases h2 : program.call outside (fuel + 3) "nat_limbs" [a2] s1 with
    | error why =>
      rw [runAll_fails _ _ _ _ _ _ _ _ (step2.1 why h2)] at ran
      cases ran
    | ok r2 =>
      obtain ⟨e2, s2⟩ := r2
      obtain ⟨b, lb, rfl, good2, arr2, -, trim2, val2, own2, kept2⟩ :=
        natLimbs_held heap _ a2 y s1 s2 e2 good1 second1 h2
      rw [runAll_on _ _ _ _ _ _ _ _ _ (step2.2 b s2 h2)] at ran
      generalize hl2 : put (put l0 "a" (some a)) "b" (some b) = l2 at ran
      have l2a : l2 "a" = some a := by rw [← hl2]; simp [put]
      have l2b : l2 "b" = some b := by rw [← hl2]; simp [put]
      have ne : a ≠ b := (kept2 a _ (own1 0 (by omega))).1
      have arr1' := array_kept s1.memory s2.memory a la arr1 (fun j hj => (kept2 a _ (own1 j hj)).2.2)
      have own1' : ∀ k, k < 24 + 8 * la.size → heap.owns s2 a (a + UInt64.ofNat k) :=
        fun k hk => (kept2 a _ (own1 k hk)).2.1
      cases h3 : outside arithmetic [a, b] s2 with
      | error why =>
        have st : Stmt.run program outside (fuel + 3)
            (.callOther (some "array") arithmetic [.var "a", .var "b"]) s2 l2 = .error why := by
          simp [Stmt.run, Expr.run, l2a, l2b, h3]
          rfl
        rw [runAll_fails _ _ _ _ _ _ _ _ st] at ran
        cases ran
      | ok r3 =>
        obtain ⟨array, s3⟩ := r3
        have st : Stmt.run program outside (fuel + 3)
            (.callOther (some "array") arithmetic [.var "a", .var "b"]) s2 l2
            = .ok (.on, s3, put l2 "array" (some array)) := by
          simp [Stmt.run, Expr.run, l2a, l2b, h3]
          rfl
        rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
        obtain ⟨good3, arr3, own3, kept3⟩ := computes a b la lb s2 array s3 good2 arr1' arr2 own1' own2 ne h3
        have step4 := call_stmt program outside (fuel + 1) "result" "nat_from" "array" natFrom array s3
          (put l2 "array" (some array)) find_natFrom (by simp [put])
        cases h4 : program.call outside (fuel + 1) "nat_from" [array] s3 with
        | error why =>
          rw [runAll_fails _ _ _ _ _ _ _ _ (step4.1 why h4)] at ran
          cases ran
        | ok r4 =>
          obtain ⟨e4, s4⟩ := r4
          obtain ⟨result, rfl, good4, held, kept4⟩ := natFrom_held heap _ array (f la lb) s3 s4 e4 good3 arr3
            (short la lb trim1 trim2 val1 val2) own3 h4
          rw [runAll_on _ _ _ _ _ _ _ _ _ (step4.2 result s4 h4)] at ran
          have st5 : Stmt.run program outside (fuel + 1) (.give (.var "result")) s4
              (put (put l2 "array" (some array)) "result" (some result))
              = .ok (.gave result, s4, put (put l2 "array" (some array)) "result" (some result)) := by
            simp [Stmt.run, Expr.run, put]
            rfl
          rw [runAll_gave _ _ _ _ _ _ _ _ _ _ st5] at ran
          injection ran with same
          injection same with eq1 eq2
          injection eq2 with eq2 eq3
          subst eq1 eq2
          refine ⟨result, rfl, good4, ?_, fun p0 q own => ?_⟩
          · rw [right la lb trim1 trim2, val1, val2] at held
            exact held
          · obtain ⟨n1, o1, m1⟩ := kept1 p0 q own
            obtain ⟨n2, o2, m2⟩ := kept2 p0 q o1
            obtain ⟨n3, o3, m3⟩ := kept3 p0 q o2 n1 n2
            obtain ⟨o4, m4⟩ := kept4 p0 q o3 n3
            exact ⟨o4, m4.trans (m3.trans (m2.trans m1))⟩

/-- `lean_nat_big_add` as a whole. -/
theorem natBigAdd_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_add" Runtime.Big.add)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.add a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_add" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x + y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_add" "rt_big_add" "" Runtime.Big.add (· + ·) rfl computes
    (fun a b _ _ => Runtime.Big.add_value a b) fuel a1 a2 x y s after ending short good first second ran

/-- `lean_nat_big_sub` as a whole; subtraction of natural numbers stops at zero. -/
theorem natBigSub_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_sub" Runtime.Big.natSub)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.natSub a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_sub" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x - y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_sub" "rt_big_sub" _ Runtime.Big.natSub (· - ·) rfl computes
    (fun a b ta tb => Runtime.Big.natSub_value a b ta tb) fuel a1 a2 x y s after ending short good first second ran

/-- `lean_nat_big_mul` as a whole. -/
theorem natBigMul_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_mul" Runtime.Big.mul)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.mul a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_mul" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x * y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_mul" "rt_big_mul" _ Runtime.Big.mul (· * ·) rfl computes
    (fun a b _ _ => Runtime.Big.mul_value a b) fuel a1 a2 x y s after ending short good first second ran

/-- `lean_nat_big_div` as a whole; a number divided by zero is zero. -/
theorem natBigDiv_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_div" Runtime.Big.natDiv)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.natDiv a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_div" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x / y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_div" "rt_big_div" _ Runtime.Big.natDiv (· / ·) rfl computes
    (fun a b _ tb => Runtime.Big.natDiv_value a b tb) fuel a1 a2 x y s after ending short good first second ran

/-- `lean_nat_big_land` as a whole. -/
theorem natBigLand_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_and" Runtime.Big.and)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.and a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_land" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x &&& y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_land" "rt_big_and" _ Runtime.Big.and (· &&& ·) rfl computes
    (fun a b _ _ => Runtime.Big.and_value a b) fuel a1 a2 x y s after ending short good first second ran

/-- `lean_nat_big_lor` as a whole. -/
theorem natBigLor_held {outside : Outside} (heap : Allocator outside)
    (computes : Computes heap "rt_big_or" Runtime.Big.or)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (short : ∀ a b, Runtime.Big.Trimmed a → Runtime.Big.Trimmed b → Runtime.Big.value a = x →
      Runtime.Big.value b = y → (Runtime.Big.or a b).size < 4294967296)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_lor" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ NatHeld heap after result (x ||| y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  natOperation_held heap "lean_nat_big_lor" "rt_big_or" _ Runtime.Big.or (· ||| ·) rfl computes
    (fun a b _ _ => Runtime.Big.or_value a b) fuel a1 a2 x y s after ending short good first second ran

/-- What is assumed of the compiled comparison: handed two different arrays of limbs, each an object of its
own, it returns what `Runtime.Big.compare` gives for them, and leaves every object but the two there and as
it was. -/
def Compares {outside : Outside} (heap : Allocator outside) : Prop :=
  ∀ (a b : UInt64) (la lb : Runtime.Big.Limbs) (t : State) (order : UInt64) (t' : State), heap.good t →
    ArrayOf t.memory a la → ArrayOf t.memory b lb →
    (∀ k, k < 24 + 8 * la.size → heap.owns t a (a + UInt64.ofNat k)) →
    (∀ k, k < 24 + 8 * lb.size → heap.owns t b (b + UInt64.ofNat k)) → a ≠ b →
    outside "rt_big_compare" [a, b] t = .ok (order, t') →
    heap.good t' ∧ order = (Runtime.Big.compare la lb).toUInt64 ∧
    ∀ p0 q, heap.owns t p0 q → p0 ≠ a → p0 ≠ b → heap.owns t' p0 q ∧ t'.memory q = t.memory q

/-- A comparison of two natural numbers, as a whole. `truth` is what the function makes of the order. -/
theorem natOrder_held {outside : Outside} (heap : Allocator outside) (name : String) (holds : Expr → Expr)
    (truth : UInt64 → UInt64)
    (found : program.functions.find? (fun f => f.name == name) = some (natOrder name holds))
    (gives : ∀ (t : State) (l : Locals) (v : UInt64), l "order" = some v →
      Expr.run t l (holds (.var "order")) = .ok (truth v))
    (compares : Compares heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel name [a1, a2] s = .ok (ending, after)) :
    ending = .gave (truth (Runtime.Big.order x y).toUInt64) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  obtain ⟨locals, ran⟩ := runAll_of_call program outside fuel name _ [a1, a2] s after ending found ran
  have ran := runAll_more program outside fuel 5 _ _ _ _ ran
  generalize hl0 : bind (fun _ => none) (natOrder name holds).parameters [a1, a2] = l0 at ran
  have l0a1 : l0 "a1" = some a1 := by rw [← hl0]; simp [natOrder, bind, put]
  have l0a2 : l0 "a2" = some a2 := by rw [← hl0]; simp [natOrder, bind, put]
  change runAll program outside (fuel + 4 + 1) [.call (some "a") "nat_limbs" [.var "a1"],
    .call (some "b") "nat_limbs" [.var "a2"], .callOther (some "order") "rt_big_compare" [.var "a", .var "b"],
    .give (holds (.var "order"))] s l0 = _ at ran
  have step1 := call_stmt program outside (fuel + 3) "a" "nat_limbs" "a1" natLimbs a1 s l0 find_natLimbs l0a1
  cases h1 : program.call outside (fuel + 3) "nat_limbs" [a1] s with
  | error why =>
    rw [runAll_fails _ _ _ _ _ _ _ _ (step1.1 why h1)] at ran
    cases ran
  | ok r1 =>
    obtain ⟨e1, s1⟩ := r1
    obtain ⟨a, la, rfl, good1, arr1, -, trim1, val1, own1, kept1⟩ :=
      natLimbs_held heap _ a1 x s s1 e1 good first h1
    rw [runAll_on _ _ _ _ _ _ _ _ _ (step1.2 a s1 h1)] at ran
    have second1 := natHeld_kept heap s s1 a2 y second (fun p0 q own => (kept1 p0 q own).2)
    have step2 := call_stmt program outside (fuel + 2) "b" "nat_limbs" "a2" natLimbs a2 s1 (put l0 "a" (some a))
      find_natLimbs (by simp [put, l0a2])
    cases h2 : program.call outside (fuel + 2) "nat_limbs" [a2] s1 with
    | error why =>
      rw [runAll_fails _ _ _ _ _ _ _ _ (step2.1 why h2)] at ran
      cases ran
    | ok r2 =>
      obtain ⟨e2, s2⟩ := r2
      obtain ⟨b, lb, rfl, good2, arr2, -, trim2, val2, own2, kept2⟩ :=
        natLimbs_held heap _ a2 y s1 s2 e2 good1 second1 h2
      rw [runAll_on _ _ _ _ _ _ _ _ _ (step2.2 b s2 h2)] at ran
      generalize hl2 : put (put l0 "a" (some a)) "b" (some b) = l2 at ran
      have l2a : l2 "a" = some a := by rw [← hl2]; simp [put]
      have l2b : l2 "b" = some b := by rw [← hl2]; simp [put]
      have ne : a ≠ b := (kept2 a _ (own1 0 (by omega))).1
      have arr1' := array_kept s1.memory s2.memory a la arr1 (fun j hj => (kept2 a _ (own1 j hj)).2.2)
      have own1' : ∀ k, k < 24 + 8 * la.size → heap.owns s2 a (a + UInt64.ofNat k) :=
        fun k hk => (kept2 a _ (own1 k hk)).2.1
      cases h3 : outside "rt_big_compare" [a, b] s2 with
      | error why =>
        have st : Stmt.run program outside (fuel + 2)
            (.callOther (some "order") "rt_big_compare" [.var "a", .var "b"]) s2 l2 = .error why := by
          simp [Stmt.run, Expr.run, l2a, l2b, h3]
          rfl
        rw [runAll_fails _ _ _ _ _ _ _ _ st] at ran
        cases ran
      | ok r3 =>
        obtain ⟨order, s3⟩ := r3
        have st : Stmt.run program outside (fuel + 2)
            (.callOther (some "order") "rt_big_compare" [.var "a", .var "b"]) s2 l2
            = .ok (.on, s3, put l2 "order" (some order)) := by
          simp [Stmt.run, Expr.run, l2a, l2b, h3]
          rfl
        rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
        obtain ⟨good3, same, kept3⟩ := compares a b la lb s2 order s3 good2 arr1' arr2 own1' own2 ne h3
        have st4 : Stmt.run program outside (fuel + 1) (.give (holds (.var "order"))) s3
            (put l2 "order" (some order)) = .ok (.gave (truth order), s3, put l2 "order" (some order)) := by
          simp [Stmt.run, gives s3 (put l2 "order" (some order)) order (by simp [put])]
          rfl
        rw [runAll_gave _ _ _ _ _ _ _ _ _ _ st4] at ran
        injection ran with eq
        injection eq with eq1 eq2
        injection eq2 with eq2 eq3
        subst eq1 eq2
        refine ⟨?_, good3, fun p0 q own => ?_⟩
        · rw [same, Runtime.Big.compare_order la lb trim1 trim2, val1, val2]
        · obtain ⟨n1, o1, m1⟩ := kept1 p0 q own
          obtain ⟨n2, o2, m2⟩ := kept2 p0 q o1
          obtain ⟨o3, m3⟩ := kept3 p0 q o2 n1 n2
          exact ⟨o3, m3.trans (m2.trans m1)⟩

/-- `lean_nat_big_eq` as a whole: 1 if the two numbers are equal, otherwise 0. -/
theorem natBigEq_held {outside : Outside} (heap : Allocator outside) (compares : Compares heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_eq" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x = y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := natOrder_held heap "lean_nat_big_eq" (Expr.eq · 1) (fun v => if v = 1 then 1 else 0) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.eq, h]; rfl) compares fuel a1 a2 x y s after ending good first
    second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.order
  by_cases h1 : x < y
  · have : x ≠ y := by omega
    simp [h1, this]
  · by_cases h2 : x = y
    · simp [h2]
    · simp [h1, h2]

/-- `lean_nat_big_le` as a whole: 1 if the first number is at most the second, otherwise 0. -/
theorem natBigLe_held {outside : Outside} (heap : Allocator outside) (compares : Compares heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_le" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x ≤ y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := natOrder_held heap "lean_nat_big_le" (Expr.ne · 2) (fun v => if v = 2 then 0 else 1) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.ne, h]; rfl) compares fuel a1 a2 x y s after ending good first
    second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.order
  by_cases h1 : x < y
  · have : x ≤ y := by omega
    simp [h1, this]
  · by_cases h2 : x = y
    · simp [h2]
    · have : ¬ x ≤ y := by omega
      simp [h1, h2, this]

/-- `lean_nat_big_lt` as a whole: 1 if the first number is below the second, otherwise 0. -/
theorem natBigLt_held {outside : Outside} (heap : Allocator outside) (compares : Compares heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Nat) (s after : State) (ending : Ending)
    (good : heap.good s) (first : NatHeld heap s a1 x) (second : NatHeld heap s a2 y)
    (ran : program.call outside fuel "lean_nat_big_lt" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x < y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := natOrder_held heap "lean_nat_big_lt" (Expr.eq · 0) (fun v => if v = 0 then 1 else 0) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.eq, h]; rfl) compares fuel a1 a2 x y s after ending good first
    second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.order
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x = y
    · simp [h2]
    · simp [h1, h2]

/-! ## Operations on integers as wholes

The same for integers. An integer goes to the arithmetic as a sign and the limbs of the number without it,
and comes back as an array of limbs with the sign as one more element. `ComputesSigned` and
`ComparesSigned` are what is assumed of those calls. -/

/-- `int_limbs` passes what a tagged word holds without its sign on to `limbs_of_word`: what that gives it
gives, and where that does not return neither does it. -/
theorem intLimbs_tagged_pass (outside : Outside) (fuel : Nat) (o : UInt64) (s : State) (tagged : o &&& 1 ≠ 0) :
    (∀ why, program.call outside (fuel + 20) "limbs_of_word" [magnitude o] s = .error why →
      program.call outside (fuel + 26) "int_limbs" [o] s = .error why) ∧
    ∀ array after, program.call outside (fuel + 20) "limbs_of_word" [magnitude o] s = .ok (.gave array, after) →
      program.call outside (fuel + 26) "int_limbs" [o] s = .ok (.gave array, after) := by
  refine ⟨fun why run => ?fails, fun array after run => ?gives⟩
  case' fails =>
    have hl := runAll_of_fails program outside (fuel + 20) "limbs_of_word" limbsOfWord [magnitude o] s why
      find_limbsOfWord run
  case' gives =>
    obtain ⟨l, hl⟩ := runAll_of_call program outside (fuel + 20) "limbs_of_word" limbsOfWord [magnitude o] s _ _
      find_limbsOfWord run
  all_goals
    by_cases neg : (2147483648 : UInt64) ≤ (o >>> 1) &&& 4294967295
    · have m : magnitude o = -((o >>> 1) &&& 4294967295) &&& 4294967295 := by simp [magnitude, neg]
      have nlt : ¬ (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_lt.mpr neg
      rw [m] at hl
      simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind,
        put, isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, nlt]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]
    · have m : magnitude o = (o >>> 1) &&& 4294967295 := by simp [magnitude, neg]
      have lt : (o >>> 1) &&& 4294967295 < 2147483648 := UInt64.not_le.mp neg
      rw [m] at hl
      simp [Program.call, find_intLimbs, find_limbsOfWord, intLimbs, runAll, Stmt.run, Expr.run, Op.run, bind,
        put, isWord, unbox, low32, top, Expr.ne, Expr.and, Expr.shr, Expr.le, tagged, lt]
      simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hl]

theorem intResult_fails (outside : Outside) (array negative : UInt64) (limbs : Runtime.Big.Limbs)
    (s : State) (n extra : Nat) (why : String) (small : limbs.size < 4294967296)
    (elements : ∀ j, (h : j < limbs.size) →
      readBytes s.memory (array + UInt64.ofNat (24 + 8 * j)) 8 = .ok (boxed limbs[j].toUInt64))
    (hn : n ≤ limbs.size)
    (range : withSign negative (Runtime.Big.lower limbs n) < -2147483648
      ∨ 2147483648 ≤ withSign negative (Runtime.Big.lower limbs n))
    (alloc : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs n)] s = .error why) :
    program.call outside (n + extra + 21) "int_result" [negative, array, UInt64.ofNat n] s = .error why := by
  have hle := trimCount_le limbs n
  have fails := bigNew_fails outside (n - trimCount limbs n + extra) _ negative array s why (by omega) alloc
  rw [show trimCount limbs n + (n - trimCount limbs n + extra) + 16 = n + extra + 16 from by omega] at fails
  exact (intResult_pass outside array negative limbs s n extra small elements hn range).1 why fails

/-- An integer as compiled Lean holds it: from -2^31 to 2^31 - 1 a tagged word holding its 32 bits; outside
that an object of its own, holding its sign and the limbs of the number without it, whose top limb is not
zero. -/
def IntHeld {outside : Outside} (heap : Allocator outside) (t : State) (o : UInt64) (i : Int) : Prop :=
  (-2147483648 ≤ i ∧ i < 2147483648 ∧ o = intWord i) ∨
  ((i < -2147483648 ∨ 2147483648 ≤ i) ∧ o &&& 1 = 0 ∧ ∃ (negative : UInt64) (limbs : Runtime.Big.Limbs),
    ObjectOf t.memory o negative limbs ∧ limbs.size < 4294967296 ∧ Runtime.Big.Trimmed limbs ∧ negative ≤ 1 ∧
    withSign negative (Runtime.Big.value limbs) = i ∧
    ∀ j, j < 16 + 4 * limbs.size → heap.owns t o (o + UInt64.ofNat j))

/-- An integer that is held stays held while every object that was there is there and as it was. -/
theorem intHeld_kept {outside : Outside} (heap : Allocator outside) (t t' : State) (o : UInt64) (i : Int)
    (held : IntHeld heap t o i)
    (kept : ∀ p0 q, heap.owns t p0 q → heap.owns t' p0 q ∧ t'.memory q = t.memory q) :
    IntHeld heap t' o i := by
  rcases held with word | ⟨range, pointer, negative, limbs, holds, small, nozero, sign, value, owned⟩
  · exact Or.inl word
  · exact Or.inr ⟨range, pointer, negative, limbs,
      object_kept t.memory t'.memory o negative limbs holds (fun j hj => (kept o _ (owned j hj)).2), small, nozero,
      sign, value, fun j hj => (kept o _ (owned j hj)).1⟩

/-- A sign of 0 or 1 on a number: which it is, from the integer. -/
theorem sign_of (negative : UInt64) (v : Nat) (i : Int) (sign : negative ≤ 1) (h : withSign negative v = i)
    (range : i < -2147483648 ∨ 2147483648 ≤ i) :
    negative = (if i < 0 then 1 else 0) ∧ v = i.natAbs := by
  by_cases z : negative = 0
  · subst z
    simp [withSign] at h
    have : ¬ i < 0 := by omega
    exact ⟨by simp [this], by omega⟩
  · have one : negative = 1 := by
      apply UInt64.toNat_inj.mp
      have a := UInt64.le_iff_toNat_le.mp sign
      have b : negative.toNat ≠ 0 := fun e => z (UInt64.toNat_inj.mp e)
      have c : (1 : UInt64).toNat = 1 := rfl
      omega
    subst one
    simp [withSign] at h
    have : i < 0 := by omega
    exact ⟨by simp [this], by omega⟩

/-- `int_sign` on an integer as compiled Lean holds it gives 1 if it is below zero and 0 if not, and changes
nothing. -/
theorem intSign_held {outside : Outside} (heap : Allocator outside) (fuel : Nat) (o : UInt64) (i : Int)
    (s after : State) (ending : Ending) (held : IntHeld heap s o i)
    (ran : program.call outside fuel "int_sign" [o] s = .ok (ending, after)) :
    ending = .gave (if i < 0 then 1 else 0) ∧ after = s := by
  have lifted := call_more program outside fuel 4 "int_sign" [o] s _ ran
  rcases held with ⟨lo, hi, rfl⟩ | ⟨range, pointer, negative, limbs, holds, -, -, sign, value, -⟩
  · rw [intSign_word outside fuel i s lo hi] at lifted
    injection lifted with same
    injection same with e1 e2
    exact ⟨e1.symm, e2.symm⟩
  · rw [intSign_object outside fuel o negative limbs s pointer holds] at lifted
    injection lifted with same
    injection same with e1 e2
    rw [(sign_of negative _ i sign value range).1] at e1
    exact ⟨e1.symm, e2.symm⟩

/-- `int_limbs` on an integer as compiled Lean holds it: if it returns, it gives an array, an object of its
own, holding limbs of the integer without its sign, with no zero limb on top; and every object that was
there is there and as it was. -/
theorem intLimbs_held {outside : Outside} (heap : Allocator outside) (fuel : Nat) (o : UInt64) (i : Int)
    (s after : State) (ending : Ending) (good : heap.good s) (held : IntHeld heap s o i)
    (ran : program.call outside fuel "int_limbs" [o] s = .ok (ending, after)) :
    ∃ array limbs, ending = .gave array ∧ heap.good after ∧ ArrayOf after.memory array limbs ∧
      limbs.size < 4294967296 ∧ Runtime.Big.Trimmed limbs ∧ Runtime.Big.value limbs = i.natAbs ∧
      (∀ k, k < 24 + 8 * limbs.size → heap.owns after array (array + UInt64.ofNat k)) ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ array ∧ heap.owns after p0 q ∧ after.memory q = s.memory q := by
  rcases held with ⟨lo, hi, rfl⟩ | ⟨range, pointer, negative, limbs, holds, small, nozero, sign, value, owned⟩
  · have two := wordLimbs_size (magnitude (intWord i))
    have lifted := call_more program outside fuel 26 "int_limbs" [intWord i] s _ ran
    have pass := intLimbs_tagged_pass outside fuel (intWord i) s (intWord_tagged i)
    cases a : outside "lean_alloc_object"
        [UInt64.ofNat (24 + 8 * (wordLimbs (magnitude (intWord i))).size)] s with
    | error why =>
      rw [pass.1 why (limbsOfWord_fails outside fuel _ s why a)] at lifted
      cases lifted
    | ok r =>
      obtain ⟨array, s'⟩ := r
      obtain ⟨memory, run, holds, frame⟩ := limbsOfWord_array outside fuel _ array s s' a
      rw [pass.2 array _ run] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', room, others⟩ := room_made heap _ s s' array memory good (by omega) a frame
      refine ⟨array, _, rfl, good', holds, by omega, wordLimbs_trimmed _, ?_, room, others⟩
      rw [wordLimbs_value, magnitude_intWord i lo hi, UInt64.toNat_ofNat']
      omega
  · obtain ⟨-, natAbs⟩ := sign_of negative _ i sign value range
    have range' : withSign negative (Runtime.Big.value limbs) < -2147483648
        ∨ 2147483648 ≤ withSign negative (Runtime.Big.value limbs) := by rw [value]; exact range
    have lifted := call_more program outside fuel (limbs.size + 19) "int_limbs" [o] s _ ran
    rw [show fuel + (limbs.size + 19) = limbs.size + fuel + 19 from by omega] at lifted
    have pass := intLimbs_object_pass outside fuel o negative limbs s pointer holds small nozero sign range'
    cases a : outside "lean_alloc_object" [UInt64.ofNat (24 + 8 * limbs.size)] s with
    | error why =>
      rw [pass.1 why (limbsOfObject_fails outside fuel limbs.size o s why a)] at lifted
      cases lifted
    | ok r =>
      obtain ⟨array, s'⟩ := r
      obtain ⟨-, -, others, room⟩ := heap.alloc _ s array s' good a
      have size : (UInt64.ofNat (24 + 8 * limbs.size)).toNat = 24 + 8 * limbs.size := by
        simp only [UInt64.toNat_ofNat']
        omega
      rw [size] at room
      obtain ⟨memory, run, holds', frame⟩ := limbsOfObject_array outside fuel o array limbs s s' small a
        (object_kept s.memory s'.memory o negative limbs holds (fun j hj => (others o _ (owned j hj)).2.2)).2.2.2
        (fun k hk j hj e => (room k hk).2 o (e ▸ owned j hj))
      rw [pass.2 array _ run] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', room', others'⟩ := room_made heap _ s s' array memory good (by omega) a frame
      exact ⟨array, limbs, rfl, good', holds', small, nozero, natAbs, room', others'⟩

/-- `int_from` on an array the arithmetic returned, limbs and then a sign, that is an object of its own: if
it returns, it gives the integer in the array (`signedValue`) as compiled Lean holds it, and every object
that was there but the array is there and as it was. -/
theorem intFrom_held {outside : Outside} (heap : Allocator outside) (fuel n : Nat) (array : UInt64)
    (limbs : Runtime.Big.Limbs) (s after : State) (ending : Ending) (good : heap.good s)
    (holds : ArrayOf s.memory array limbs) (size : limbs.size = n + 1) (small : limbs.size < 4294967296)
    (owned : ∀ k, k < 24 + 8 * limbs.size → heap.owns s array (array + UInt64.ofNat k))
    (ran : program.call outside fuel "int_from" [array] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧
      IntHeld heap after result (Runtime.Big.signedValue limbs) ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ array → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have sv := signedValue_topSign limbs n size
  have sign := topSign_le limbs n
  have hn : n ≤ limbs.size := by omega
  by_cases fits : -2147483648 ≤ Runtime.Big.signedValue limbs ∧ Runtime.Big.signedValue limbs < 2147483648
  · have run := intResult_word outside array (topSign limbs n) limbs s n fuel (by omega) holds.2.2 hn
      (by rw [← sv]; exact fits.1) (by rw [← sv]; exact fits.2)
    have pass := (intFrom_pass outside (n + fuel + 8) n array limbs s holds size small).2 _ _ run
    have lifted := call_more program outside fuel (n + 14) "int_from" [array] s _ ran
    rw [show fuel + (n + 14) = n + fuel + 8 + 6 from by omega] at lifted
    cases d : outside "lean_dec" [array] s with
    | error why =>
      rw [pass.1 why d] at lifted
      cases lifted
    | ok r =>
      obtain ⟨unused, after'⟩ := r
      rw [pass.2 unused after' d] at lifted
      injection lifted with same
      injection same with e1 e2
      subst e1 e2
      obtain ⟨good', others⟩ := heap.dec array limbs s unused after' good holds owned d
      exact ⟨_, rfl, good', Or.inl ⟨fits.1, fits.2, by rw [sv]⟩, others⟩
  · have range : Runtime.Big.signedValue limbs < -2147483648 ∨ 2147483648 ≤ Runtime.Big.signedValue limbs := by
      omega
    have range' : withSign (topSign limbs n) (Runtime.Big.lower limbs n) < -2147483648
        ∨ 2147483648 ≤ withSign (topSign limbs n) (Runtime.Big.lower limbs n) := by rw [← sv]; exact range
    have hle := trimCount_le limbs n
    have lifted := call_more program outside fuel (n + 25) "int_from" [array] s _ ran
    rw [show fuel + (n + 25) = n + fuel + 19 + 6 from by omega] at lifted
    have pass := intFrom_pass outside (n + fuel + 19) n array limbs s holds size small
    cases a : outside "lean_alloc_object" [UInt64.ofNat (16 + 4 * trimCount limbs n)] s with
    | error why =>
      rw [pass.1 why (intResult_fails outside array _ limbs s n fuel why small holds.2.2 hn range' a)] at lifted
      cases lifted
    | ok r =>
      obtain ⟨o, s'⟩ := r
      obtain ⟨-, even, others, room⟩ := heap.alloc _ s o s' good a
      have bytes : (UInt64.ofNat (16 + 4 * trimCount limbs n)).toNat = 16 + 4 * trimCount limbs n := by
        simp only [UInt64.toNat_ofNat']
        omega
      rw [bytes] at room
      obtain ⟨memory, run, object, frame⟩ := intResult_object outside array (topSign limbs n) o limbs s s' n fuel
        small holds.2.2 hn sign range' a
        (fun j hj => (others array _ (owned j hj)).2.2)
        (fun k hk j hj e => (room k hk).2 array (e ▸ owned j hj))
      obtain ⟨good', room', others'⟩ := room_made heap _ s s' o memory good (by omega) a frame
      have pass' := pass.2 o _ run
      cases d : outside "lean_dec" [array] { s' with memory := memory } with
      | error why =>
        rw [pass'.1 why d] at lifted
        cases lifted
      | ok r =>
        obtain ⟨unused, after'⟩ := r
        rw [pass'.2 unused after' d] at lifted
        injection lifted with same
        injection same with e1 e2
        subst e1 e2
        obtain ⟨good'', others''⟩ := heap.dec array limbs { s' with memory := memory } unused after' good'
          (array_kept s.memory memory array limbs holds (fun j hj => (others' array _ (owned j hj)).2.2))
          (fun k hk => (others' array _ (owned k hk)).2.1) d
        have apart : o ≠ array := fun e => (others' array _ (owned 0 (by omega))).1 e.symm
        have ksize := keptLimbs_size limbs n hn
        refine ⟨o, rfl, good'', Or.inr ⟨range, even, topSign limbs n, keptLimbs limbs n, ?_, by omega,
          keptLimbs_trimmed limbs n hn, sign, ?_, ?_⟩, fun p0 q own ne => ?_⟩
        · exact object_kept memory after'.memory o _ _ object
            (fun j hj => (others'' o _ (room' j (by omega)) apart).2)
        · rw [keptLimbs_value limbs n hn, sv]
        · exact fun j hj => (others'' o _ (room' j (by omega)) apart).1
        · obtain ⟨-, own', mem⟩ := others' p0 q own
          obtain ⟨own'', mem'⟩ := others'' p0 q own' ne
          exact ⟨own'', mem'.trans mem⟩

/-- What is assumed of a call into the compiled arithmetic on integers: handed two signs, each 0 or 1, and
two different arrays of limbs, each an object of its own, it returns an array holding what the Lean
function gives for them, which is an object of its own and none of those that were there besides the two;
and it leaves every object but the two there and as it was. -/
def ComputesSigned {outside : Outside} (heap : Allocator outside) (name : String)
    (f : UInt8 → Runtime.Big.Limbs → UInt8 → Runtime.Big.Limbs → Runtime.Big.Limbs) : Prop :=
  ∀ (sa a sb b : UInt64) (la lb : Runtime.Big.Limbs) (t : State) (array : UInt64) (t' : State), heap.good t →
    sa ≤ 1 → sb ≤ 1 → ArrayOf t.memory a la → ArrayOf t.memory b lb →
    (∀ k, k < 24 + 8 * la.size → heap.owns t a (a + UInt64.ofNat k)) →
    (∀ k, k < 24 + 8 * lb.size → heap.owns t b (b + UInt64.ofNat k)) → a ≠ b →
    outside name [sa, a, sb, b] t = .ok (array, t') →
    heap.good t' ∧ ArrayOf t'.memory array (f sa.toUInt8 la sb.toUInt8 lb) ∧
    (∀ k, k < 24 + 8 * (f sa.toUInt8 la sb.toUInt8 lb).size → heap.owns t' array (array + UInt64.ofNat k)) ∧
    ∀ p0 q, heap.owns t p0 q → p0 ≠ a → p0 ≠ b →
      p0 ≠ array ∧ heap.owns t' p0 q ∧ t'.memory q = t.memory q

/-- The same of the compiled comparison of integers: it returns what `Runtime.Big.intCompare` gives. -/
def ComparesSigned {outside : Outside} (heap : Allocator outside) : Prop :=
  ∀ (sa a sb b : UInt64) (la lb : Runtime.Big.Limbs) (t : State) (order : UInt64) (t' : State), heap.good t →
    sa ≤ 1 → sb ≤ 1 → ArrayOf t.memory a la → ArrayOf t.memory b lb →
    (∀ k, k < 24 + 8 * la.size → heap.owns t a (a + UInt64.ofNat k)) →
    (∀ k, k < 24 + 8 * lb.size → heap.owns t b (b + UInt64.ofNat k)) → a ≠ b →
    outside "rt_big_int_compare" [sa, a, sb, b] t = .ok (order, t') →
    heap.good t' ∧ order = (Runtime.Big.intCompare sa.toUInt8 la sb.toUInt8 lb).toUInt64 ∧
    ∀ p0 q, heap.owns t p0 q → p0 ≠ a → p0 ≠ b → heap.owns t' p0 q ∧ t'.memory q = t.memory q

/-- The sign this program passes for an integer: 1 if it is below zero, otherwise 0. -/
def signOf (i : Int) : UInt64 := if i < 0 then 1 else 0

theorem signOf_le (i : Int) : signOf i ≤ 1 := by
  unfold signOf
  split <;> decide

theorem signOf_isSign (i : Int) : Runtime.Big.IsSign (signOf i).toUInt8 := by
  unfold signOf
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- That sign, on the limbs of the integer without its sign, is the integer. -/
theorem intOf_signOf (i : Int) (limbs : Runtime.Big.Limbs) (h : Runtime.Big.value limbs = i.natAbs) :
    Runtime.Big.intOf ((signOf i).toUInt8 != 0) limbs = i := by
  unfold signOf
  by_cases neg : i < 0
  · simp [neg, Runtime.Big.intOf, h]
    omega
  · simp [neg, Runtime.Big.intOf, h]
    omega

/-- The start of every operation on two integers: the limbs and the sign of each. If the rest returns, it
ran from a state with the two arrays in it, each an object of its own, and locals holding them and the
signs. -/
theorem intArguments {outside : Outside} (heap : Allocator outside) (fuel : Nat) (rest : List Stmt)
    (a1 a2 : UInt64) (x y : Int) (s : State) (l0 : Locals) (r : Ending × State × Locals) (good : heap.good s)
    (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (l0a1 : l0 "a1" = some a1) (l0a2 : l0 "a2" = some a2)
    (ran : runAll program outside (fuel + 5) (.call (some "a") "int_limbs" [.var "a1"] ::
      .call (some "sign1") "int_sign" [.var "a1"] :: .call (some "b") "int_limbs" [.var "a2"] ::
      .call (some "sign2") "int_sign" [.var "a2"] :: rest) s l0 = .ok r) :
    ∃ a b la lb s2 l2, runAll program outside (fuel + 1) rest s2 l2 = .ok r ∧
      l2 "a" = some a ∧ l2 "sign1" = some (signOf x) ∧ l2 "b" = some b ∧ l2 "sign2" = some (signOf y) ∧
      heap.good s2 ∧ ArrayOf s2.memory a la ∧ ArrayOf s2.memory b lb ∧
      Runtime.Big.Trimmed la ∧ Runtime.Big.Trimmed lb ∧ lb.size < 4294967296 ∧
      Runtime.Big.value la = x.natAbs ∧ Runtime.Big.value lb = y.natAbs ∧
      (∀ k, k < 24 + 8 * la.size → heap.owns s2 a (a + UInt64.ofNat k)) ∧
      (∀ k, k < 24 + 8 * lb.size → heap.owns s2 b (b + UInt64.ofNat k)) ∧ a ≠ b ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ a ∧ p0 ≠ b ∧ heap.owns s2 p0 q ∧ s2.memory q = s.memory q := by
  have step1 := call_stmt program outside (fuel + 3) "a" "int_limbs" "a1" intLimbs a1 s l0 find_intLimbs l0a1
  cases h1 : program.call outside (fuel + 3) "int_limbs" [a1] s with
  | error why =>
    rw [runAll_fails _ _ _ _ _ _ _ _ (step1.1 why h1)] at ran
    cases ran
  | ok r1 =>
    obtain ⟨e1, s1⟩ := r1
    obtain ⟨a, la, rfl, good1, arr1, -, trim1, val1, own1, kept1⟩ :=
      intLimbs_held heap _ a1 x s s1 e1 good first h1
    rw [runAll_on _ _ _ _ _ _ _ _ _ (step1.2 a s1 h1)] at ran
    have kept1' : ∀ p0 q, heap.owns s p0 q → heap.owns s1 p0 q ∧ s1.memory q = s.memory q :=
      fun p0 q own => (kept1 p0 q own).2
    have first1 := intHeld_kept heap s s1 a1 x first kept1'
    have second1 := intHeld_kept heap s s1 a2 y second kept1'
    have step2 := call_stmt program outside (fuel + 2) "sign1" "int_sign" "a1" intSign a1 s1
      (put l0 "a" (some a)) find_intSign (by simp [put, l0a1])
    cases h2 : program.call outside (fuel + 2) "int_sign" [a1] s1 with
    | error why =>
      rw [runAll_fails _ _ _ _ _ _ _ _ (step2.1 why h2)] at ran
      cases ran
    | ok r2 =>
      obtain ⟨e2, s1'⟩ := r2
      obtain ⟨rfl, same⟩ := intSign_held heap _ a1 x s1 s1' e2 first1 h2
      rw [same] at h2
      rw [runAll_on _ _ _ _ _ _ _ _ _ (step2.2 _ s1 h2)] at ran
      have step3 := call_stmt program outside (fuel + 1) "b" "int_limbs" "a2" intLimbs a2 s1
        (put (put l0 "a" (some a)) "sign1" (some (if x < 0 then 1 else 0))) find_intLimbs
        (by simp [put, l0a2])
      cases h3 : program.call outside (fuel + 1) "int_limbs" [a2] s1 with
      | error why =>
        rw [runAll_fails _ _ _ _ _ _ _ _ (step3.1 why h3)] at ran
        cases ran
      | ok r3 =>
        obtain ⟨e3, s2⟩ := r3
        obtain ⟨b, lb, rfl, good2, arr2, small2, trim2, val2, own2, kept2⟩ :=
          intLimbs_held heap _ a2 y s1 s2 e3 good1 second1 h3
        rw [runAll_on _ _ _ _ _ _ _ _ _ (step3.2 b s2 h3)] at ran
        have second2 := intHeld_kept heap s1 s2 a2 y second1 (fun p0 q own => (kept2 p0 q own).2)
        have step4 := call_stmt program outside fuel "sign2" "int_sign" "a2" intSign a2 s2
          (put (put (put l0 "a" (some a)) "sign1" (some (if x < 0 then 1 else 0))) "b" (some b)) find_intSign
          (by simp [put, l0a2])
        cases h4 : program.call outside fuel "int_sign" [a2] s2 with
        | error why =>
          rw [runAll_fails _ _ _ _ _ _ _ _ (step4.1 why h4)] at ran
          cases ran
        | ok r4 =>
          obtain ⟨e4, s2'⟩ := r4
          obtain ⟨rfl, same⟩ := intSign_held heap _ a2 y s2 s2' e4 second2 h4
          rw [same] at h4
          rw [runAll_on _ _ _ _ _ _ _ _ _ (step4.2 _ s2 h4)] at ran
          refine ⟨a, b, la, lb, s2, _, ran, by simp [put], by simp [put, signOf], by simp [put],
            by simp [put, signOf], good2,
            array_kept s1.memory s2.memory a la arr1 (fun j hj => (kept2 a _ (own1 j hj)).2.2), arr2, trim1, trim2,
            small2, val1, val2, fun k hk => (kept2 a _ (own1 k hk)).2.1, own2,
            (kept2 a _ (own1 0 (by omega))).1, fun p0 q own => ?_⟩
          obtain ⟨n1, o1, m1⟩ := kept1 p0 q own
          obtain ⟨n2, o2, m2⟩ := kept2 p0 q o1
          exact ⟨n1, n2, o2, m2.trans m1⟩

/-- The end of an operation on two integers that computes: the call into the arithmetic, and `int_from` on
what it returns. -/
theorem intTail {outside : Outside} (heap : Allocator outside) (arithmetic : String)
    (f : UInt8 → Runtime.Big.Limbs → UInt8 → Runtime.Big.Limbs → Runtime.Big.Limbs)
    (computes : ComputesSigned heap arithmetic f) (fuel : Nat) (a b sa sb : UInt64)
    (la lb : Runtime.Big.Limbs) (s2 after : State) (l2 locals : Locals) (ending : Ending)
    (l2a : l2 "a" = some a) (l2sa : l2 "sign1" = some sa) (l2b : l2 "b" = some b) (l2sb : l2 "sign2" = some sb)
    (good2 : heap.good s2) (arr1 : ArrayOf s2.memory a la) (arr2 : ArrayOf s2.memory b lb)
    (own1 : ∀ k, k < 24 + 8 * la.size → heap.owns s2 a (a + UInt64.ofNat k))
    (own2 : ∀ k, k < 24 + 8 * lb.size → heap.owns s2 b (b + UInt64.ofNat k)) (ne : a ≠ b)
    (hsa : sa ≤ 1) (hsb : sb ≤ 1) (nonempty : (f sa.toUInt8 la sb.toUInt8 lb).size ≠ 0)
    (short : (f sa.toUInt8 la sb.toUInt8 lb).size < 4294967296)
    (ran : runAll program outside (fuel + 4) [.callOther (some "array") arithmetic
        [.var "sign1", .var "a", .var "sign2", .var "b"],
      .call (some "result") "int_from" [.var "array"], .give (.var "result")] s2 l2
      = .ok (ending, after, locals)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧
      IntHeld heap after result (Runtime.Big.signedValue (f sa.toUInt8 la sb.toUInt8 lb)) ∧
      ∀ p0 q, heap.owns s2 p0 q → p0 ≠ a → p0 ≠ b →
        heap.owns after p0 q ∧ after.memory q = s2.memory q := by
  cases h3 : outside arithmetic [sa, a, sb, b] s2 with
  | error why =>
    have st : Stmt.run program outside (fuel + 3) (.callOther (some "array") arithmetic
        [.var "sign1", .var "a", .var "sign2", .var "b"]) s2 l2 = .error why := by
      simp [Stmt.run, Expr.run, l2a, l2b, l2sa, l2sb, h3]
      rfl
    rw [runAll_fails _ _ _ _ _ _ _ _ st] at ran
    cases ran
  | ok r3 =>
    obtain ⟨array, s3⟩ := r3
    have st : Stmt.run program outside (fuel + 3) (.callOther (some "array") arithmetic
        [.var "sign1", .var "a", .var "sign2", .var "b"]) s2 l2
        = .ok (.on, s3, put l2 "array" (some array)) := by
      simp [Stmt.run, Expr.run, l2a, l2b, l2sa, l2sb, h3]
      rfl
    rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
    obtain ⟨good3, arr3, own3, kept3⟩ := computes sa a sb b la lb s2 array s3 good2 hsa hsb arr1 arr2 own1 own2
      ne h3
    have step4 := call_stmt program outside (fuel + 1) "result" "int_from" "array" intFrom array s3
      (put l2 "array" (some array)) find_intFrom (by simp [put])
    cases h4 : program.call outside (fuel + 1) "int_from" [array] s3 with
    | error why =>
      rw [runAll_fails _ _ _ _ _ _ _ _ (step4.1 why h4)] at ran
      cases ran
    | ok r4 =>
      obtain ⟨e4, s4⟩ := r4
      obtain ⟨result, rfl, good4, held, kept4⟩ := intFrom_held heap _
        ((f sa.toUInt8 la sb.toUInt8 lb).size - 1) array _ s3 s4 e4 good3 arr3 (by omega) short own3 h4
      rw [runAll_on _ _ _ _ _ _ _ _ _ (step4.2 result s4 h4)] at ran
      have st5 : Stmt.run program outside (fuel + 1) (.give (.var "result")) s4
          (put (put l2 "array" (some array)) "result" (some result))
          = .ok (.gave result, s4, put (put l2 "array" (some array)) "result" (some result)) := by
        simp [Stmt.run, Expr.run, put]
        rfl
      rw [runAll_gave _ _ _ _ _ _ _ _ _ _ st5] at ran
      injection ran with same
      injection same with eq1 eq2
      injection eq2 with eq2 eq3
      subst eq1 eq2
      refine ⟨result, rfl, good4, held, fun p0 q own na nb => ?_⟩
      obtain ⟨n3, o3, m3⟩ := kept3 p0 q own na nb
      obtain ⟨o4, m4⟩ := kept4 p0 q o3 n3
      exact ⟨o4, m4.trans m3⟩

theorem signed_size (negative : Bool) (limbs : Runtime.Big.Limbs) :
    (Runtime.Big.signed negative limbs).size ≠ 0 := by
  simp [Runtime.Big.signed]

theorem intAdd_size (sa : UInt8) (la : Runtime.Big.Limbs) (sb : UInt8) (lb : Runtime.Big.Limbs) :
    (Runtime.Big.intAdd sa la sb lb).size ≠ 0 := by
  simp only [Runtime.Big.intAdd]
  repeat' split
  all_goals exact signed_size _ _

theorem intMul_size (sa : UInt8) (la : Runtime.Big.Limbs) (sb : UInt8) (lb : Runtime.Big.Limbs) :
    (Runtime.Big.intMul sa la sb lb).size ≠ 0 := signed_size _ _

theorem intEdiv_size (sa : UInt8) (la : Runtime.Big.Limbs) (sb : UInt8) (lb : Runtime.Big.Limbs) :
    (Runtime.Big.intEdiv sa la sb lb).size ≠ 0 := by
  simp only [Runtime.Big.intEdiv]
  repeat' split
  all_goals exact signed_size _ _

/-- An operation on two integers that computes, as a whole. With `minus` the second is taken with its sign
turned round. -/
theorem intOperation_held {outside : Outside} (heap : Allocator outside) (name arithmetic : String)
    (minus : Bool) (about : String)
    (f : UInt8 → Runtime.Big.Limbs → UInt8 → Runtime.Big.Limbs → Runtime.Big.Limbs) (g : Int → Int → Int)
    (found : program.functions.find? (fun f => f.name == name)
      = some (intOperation name arithmetic minus about))
    (computes : ComputesSigned heap arithmetic f)
    (right : ∀ sa la sb lb, Runtime.Big.IsSign sa → Runtime.Big.IsSign sb → Runtime.Big.Trimmed la →
      Runtime.Big.Trimmed lb → Runtime.Big.signedValue (f sa la sb lb)
        = g (Runtime.Big.intOf (sa != 0) la) (Runtime.Big.intOf (sb != 0) lb))
    (nonempty : ∀ sa la sb lb, (f sa la sb lb).size ≠ 0)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (short : ∀ sa la sb lb, Runtime.Big.Trimmed la → Runtime.Big.Trimmed lb →
      Runtime.Big.value la = x.natAbs → Runtime.Big.value lb = y.natAbs → (f sa la sb lb).size < 4294967296)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel name [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧
      IntHeld heap after result (g x (if minus then -y else y)) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  obtain ⟨locals, ran⟩ := runAll_of_call program outside fuel name _ [a1, a2] s after ending found ran
  have ran := runAll_more program outside fuel 9 _ _ _ _ ran
  generalize hl0 : bind (fun _ => none) (intOperation name arithmetic minus about).parameters [a1, a2] = l0
    at ran
  have l0a1 : l0 "a1" = some a1 := by rw [← hl0]; simp [intOperation, bind, put]
  have l0a2 : l0 "a2" = some a2 := by rw [← hl0]; simp [intOperation, bind, put]
  -- With or without the turn of the sign, the end runs with the second number's sign as it is to be used.
  have reach : ∃ a b la lb s2 l3, runAll program outside (fuel + 5) [.callOther (some "array") arithmetic
        [.var "sign1", .var "a", .var "sign2", .var "b"],
        .call (some "result") "int_from" [.var "array"], .give (.var "result")] s2 l3
        = .ok (ending, after, locals) ∧
      l3 "a" = some a ∧ l3 "sign1" = some (signOf x) ∧ l3 "b" = some b ∧
      l3 "sign2" = some (signOf (if minus then -y else y)) ∧
      heap.good s2 ∧ ArrayOf s2.memory a la ∧ ArrayOf s2.memory b lb ∧
      Runtime.Big.Trimmed la ∧ Runtime.Big.Trimmed lb ∧
      Runtime.Big.value la = x.natAbs ∧ Runtime.Big.value lb = y.natAbs ∧
      (∀ k, k < 24 + 8 * la.size → heap.owns s2 a (a + UInt64.ofNat k)) ∧
      (∀ k, k < 24 + 8 * lb.size → heap.owns s2 b (b + UInt64.ofNat k)) ∧ a ≠ b ∧
      ∀ p0 q, heap.owns s p0 q → p0 ≠ a ∧ p0 ≠ b ∧ heap.owns s2 p0 q ∧ s2.memory q = s.memory q := by
    cases minus with
    | false =>
      obtain ⟨a, b, la, lb, s2, l2, ran, l2a, l2sa, l2b, l2sb, good2, arr1, arr2, trim1, trim2, -, val1, val2,
        own1, own2, ne, kept⟩ := intArguments heap (fuel + 4) [.callOther (some "array") arithmetic
          [.var "sign1", .var "a", .var "sign2", .var "b"],
          .call (some "result") "int_from" [.var "array"], .give (.var "result")] a1 a2 x y s l0 _ good first
          second l0a1 l0a2 ran
      exact ⟨a, b, la, lb, s2, l2, ran, l2a, l2sa, l2b, l2sb, good2, arr1, arr2, trim1, trim2, val1, val2, own1,
        own2, ne, kept⟩
    | true =>
      obtain ⟨a, b, la, lb, s2, l2, ran, l2a, l2sa, l2b, l2sb, good2, arr1, arr2, trim1, trim2, small2, val1,
        val2, own1, own2, ne, kept⟩ := intArguments heap (fuel + 5)
          [.branch (Expr.ne (sizeOf "b") 0) [.set "sign2" (1 - "sign2")] [],
          .callOther (some "array") arithmetic [.var "sign1", .var "a", .var "sign2", .var "b"],
          .call (some "result") "int_from" [.var "array"], .give (.var "result")] a1 a2 x y s l0 _ good first
          second l0a1 l0a2 (runAll_more program outside (fuel + 9) 1 _ _ _ _ ran)
      have hsize := arr2.2.1
      by_cases z : lb.size = 0
      · have zero : UInt64.ofNat lb.size = 0 := by rw [z]; rfl
        rw [zero] at hsize
        have st : Stmt.run program outside (fuel + 5)
            (.branch (Expr.ne (sizeOf "b") 0) [.set "sign2" (1 - "sign2")] []) s2 l2 = .ok (.on, s2, l2) := by
          simp [Stmt.run, runAll, Expr.run, Op.run, Expr.ne, sizeOf, l2b, hsize]
          rfl
        rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
        have y0 : y = 0 := by
          have := Runtime.Big.value_lt_pow lb
          rw [z, Nat.pow_zero] at this
          omega
        refine ⟨a, b, la, lb, s2, l2, ran, l2a, l2sa, l2b, ?_, good2, arr1, arr2, trim1, trim2, val1, val2, own1,
          own2, ne, kept⟩
        rw [l2sb, y0]
        rfl
      · have nz : UInt64.ofNat lb.size ≠ 0 := word_ne lb.size 0 small2 (by omega) z
        have st : Stmt.run program outside (fuel + 5)
            (.branch (Expr.ne (sizeOf "b") 0) [.set "sign2" (1 - "sign2")] []) s2 l2
            = .ok (.on, s2, put l2 "sign2" (some (1 - signOf y))) := by
          simp [Stmt.run, runAll, Expr.run, Op.run, Expr.ne, sizeOf, l2b, l2sb, hsize]
          simp [Bind.bind, Except.bind, nz]
          rfl
        rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
        have ynz : y ≠ 0 := by
          have low := Runtime.Big.pow_le_value lb z trim2
          have pos : 0 < 4294967296 ^ (lb.size - 1) := Nat.pow_pos (by decide)
          omega
        have flip : 1 - signOf y = signOf (-y) := by
          unfold signOf
          by_cases h : y < 0
          · have : ¬ -y < 0 := by omega
            simp only [h, this, ↓reduceIte]
            rfl
          · have : -y < 0 := by omega
            simp only [h, this, ↓reduceIte]
            rfl
        refine ⟨a, b, la, lb, s2, _, ran, by simp [put, l2a], by simp [put, l2sa], by simp [put, l2b],
          by simp [put, flip], good2, arr1, arr2, trim1, trim2, val1, val2, own1, own2, ne, kept⟩
  obtain ⟨a, b, la, lb, s2, l3, ran, l3a, l3sa, l3b, l3sb, good2, arr1, arr2, trim1, trim2, val1, val2, own1,
    own2, ne, kept⟩ := reach
  have val2' : Runtime.Big.value lb = (if minus = true then -y else y).natAbs := by
    cases minus <;> simp [val2]
  generalize (if minus = true then -y else y) = y' at l3sb val2' ⊢
  obtain ⟨result, rfl, good4, held, kept4⟩ := intTail heap arithmetic f computes (fuel + 1) a b (signOf x)
    (signOf y') la lb s2 after l3 locals ending l3a l3sa l3b l3sb good2 arr1 arr2 own1 own2 ne (signOf_le x)
    (signOf_le y') (nonempty _ _ _ _) (short _ la _ lb trim1 trim2 val1 val2) ran
  rw [right _ la _ lb (signOf_isSign x) (signOf_isSign y') trim1 trim2, intOf_signOf x la val1,
    intOf_signOf y' lb val2'] at held
  refine ⟨result, rfl, good4, held, fun p0 q own => ?_⟩
  obtain ⟨n1, n2, o2, m2⟩ := kept p0 q own
  obtain ⟨o4, m4⟩ := kept4 p0 q o2 n1 n2
  exact ⟨o4, m4.trans m2⟩

/-- `lean_int_big_add` as a whole. -/
theorem intBigAdd_held {outside : Outside} (heap : Allocator outside)
    (computes : ComputesSigned heap "rt_big_int_add" Runtime.Big.intAdd)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (short : ∀ sa la sb lb, Runtime.Big.Trimmed la → Runtime.Big.Trimmed lb →
      Runtime.Big.value la = x.natAbs → Runtime.Big.value lb = y.natAbs →
      (Runtime.Big.intAdd sa la sb lb).size < 4294967296)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_add" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ IntHeld heap after result (x + y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  intOperation_held heap "lean_int_big_add" "rt_big_int_add" false _ Runtime.Big.intAdd (· + ·) rfl computes
    (fun sa la sb lb ha hb ta tb => Runtime.Big.intAdd_value sa la sb lb ha hb ta tb) intAdd_size fuel a1 a2 x y s after
    ending short good first second ran

/-- `lean_int_big_sub` as a whole: the sum with the second number's sign turned round. -/
theorem intBigSub_held {outside : Outside} (heap : Allocator outside)
    (computes : ComputesSigned heap "rt_big_int_add" Runtime.Big.intAdd)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (short : ∀ sa la sb lb, Runtime.Big.Trimmed la → Runtime.Big.Trimmed lb →
      Runtime.Big.value la = x.natAbs → Runtime.Big.value lb = y.natAbs →
      (Runtime.Big.intAdd sa la sb lb).size < 4294967296)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_sub" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ IntHeld heap after result (x - y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  intOperation_held heap "lean_int_big_sub" "rt_big_int_add" true _ Runtime.Big.intAdd (· + ·) rfl computes
    (fun sa la sb lb ha hb ta tb => Runtime.Big.intAdd_value sa la sb lb ha hb ta tb) intAdd_size fuel a1 a2 x y s after
    ending short good first second ran

/-- `lean_int_big_mul` as a whole. -/
theorem intBigMul_held {outside : Outside} (heap : Allocator outside)
    (computes : ComputesSigned heap "rt_big_int_mul" Runtime.Big.intMul)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (short : ∀ sa la sb lb, Runtime.Big.Trimmed la → Runtime.Big.Trimmed lb →
      Runtime.Big.value la = x.natAbs → Runtime.Big.value lb = y.natAbs →
      (Runtime.Big.intMul sa la sb lb).size < 4294967296)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_mul" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ IntHeld heap after result (x * y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  intOperation_held heap "lean_int_big_mul" "rt_big_int_mul" false _ Runtime.Big.intMul (· * ·) rfl computes
    (fun sa la sb lb ha hb _ _ => Runtime.Big.intMul_value sa la sb lb ha hb) intMul_size fuel a1 a2 x y s after
    ending short good first second ran

/-- `lean_int_big_ediv` as a whole: `Int`'s division, whose remainder is never negative; by zero it gives zero. -/
theorem intBigEdiv_held {outside : Outside} (heap : Allocator outside)
    (computes : ComputesSigned heap "rt_big_int_ediv" Runtime.Big.intEdiv)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (short : ∀ sa la sb lb, Runtime.Big.Trimmed la → Runtime.Big.Trimmed lb →
      Runtime.Big.value la = x.natAbs → Runtime.Big.value lb = y.natAbs →
      (Runtime.Big.intEdiv sa la sb lb).size < 4294967296)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_ediv" [a1, a2] s = .ok (ending, after)) :
    ∃ result, ending = .gave result ∧ heap.good after ∧ IntHeld heap after result (x / y) ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q :=
  intOperation_held heap "lean_int_big_ediv" "rt_big_int_ediv" false _ Runtime.Big.intEdiv (· / ·) rfl computes
    (fun sa la sb lb ha hb _ tb => Runtime.Big.intEdiv_value sa la sb lb ha hb tb) intEdiv_size fuel a1 a2 x y s after
    ending short good first second ran

/-- A comparison of two integers, as a whole. `truth` is what the function makes of the order. -/
theorem intOrder_held {outside : Outside} (heap : Allocator outside) (name : String) (holds : Expr → Expr)
    (truth : UInt64 → UInt64)
    (found : program.functions.find? (fun f => f.name == name) = some (Mini.Number.intOrder name holds))
    (gives : ∀ (t : State) (l : Locals) (v : UInt64), l "order" = some v →
      Expr.run t l (holds (.var "order")) = .ok (truth v))
    (compares : ComparesSigned heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel name [a1, a2] s = .ok (ending, after)) :
    ending = .gave (truth (Runtime.Big.intOrder x y).toUInt64) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  obtain ⟨locals, ran⟩ := runAll_of_call program outside fuel name _ [a1, a2] s after ending found ran
  have ran := runAll_more program outside fuel 7 _ _ _ _ ran
  generalize hl0 : bind (fun _ => none) (Mini.Number.intOrder name holds).parameters [a1, a2] = l0 at ran
  have l0a1 : l0 "a1" = some a1 := by rw [← hl0]; simp [Mini.Number.intOrder, bind, put]
  have l0a2 : l0 "a2" = some a2 := by rw [← hl0]; simp [Mini.Number.intOrder, bind, put]
  obtain ⟨a, b, la, lb, s2, l2, ran, l2a, l2sa, l2b, l2sb, good2, arr1, arr2, trim1, trim2, -, val1, val2, own1,
    own2, ne, kept⟩ := intArguments heap (fuel + 2) [.callOther (some "order") "rt_big_int_compare"
      [.var "sign1", .var "a", .var "sign2", .var "b"], .give (holds (.var "order"))] a1 a2 x y s l0 _ good first
      second l0a1 l0a2 ran
  cases h3 : outside "rt_big_int_compare" [signOf x, a, signOf y, b] s2 with
  | error why =>
    have st : Stmt.run program outside (fuel + 2) (.callOther (some "order") "rt_big_int_compare"
        [.var "sign1", .var "a", .var "sign2", .var "b"]) s2 l2 = .error why := by
      simp [Stmt.run, Expr.run, l2a, l2b, l2sa, l2sb, h3]
      rfl
    rw [runAll_fails _ _ _ _ _ _ _ _ st] at ran
    cases ran
  | ok r3 =>
    obtain ⟨order, s3⟩ := r3
    have st : Stmt.run program outside (fuel + 2) (.callOther (some "order") "rt_big_int_compare"
        [.var "sign1", .var "a", .var "sign2", .var "b"]) s2 l2
        = .ok (.on, s3, put l2 "order" (some order)) := by
      simp [Stmt.run, Expr.run, l2a, l2b, l2sa, l2sb, h3]
      rfl
    rw [runAll_on _ _ _ _ _ _ _ _ _ st] at ran
    obtain ⟨good3, same, kept3⟩ := compares (signOf x) a (signOf y) b la lb s2 order s3 good2 (signOf_le x)
      (signOf_le y) arr1 arr2 own1 own2 ne h3
    have st4 : Stmt.run program outside (fuel + 1) (.give (holds (.var "order"))) s3
        (put l2 "order" (some order)) = .ok (.gave (truth order), s3, put l2 "order" (some order)) := by
      simp [Stmt.run, gives s3 (put l2 "order" (some order)) order (by simp [put])]
      rfl
    rw [runAll_gave _ _ _ _ _ _ _ _ _ _ st4] at ran
    injection ran with eq
    injection eq with eq1 eq2
    injection eq2 with eq2 eq3
    subst eq1 eq2
    have notzero : ∀ (i : Int) (limbs : Runtime.Big.Limbs), Runtime.Big.value limbs = i.natAbs →
        (signOf i).toUInt8 = 1 → Runtime.Big.value limbs ≠ 0 := by
      intro i limbs hv one
      have neg : i < 0 := by
        refine Decidable.byContradiction (fun h => ?_)
        simp only [signOf, h, ↓reduceIte] at one
        exact absurd one (by decide)
      omega
    refine ⟨?_, good3, fun p0 q own => ?_⟩
    · rw [same, Runtime.Big.intCompare_order _ la _ lb (signOf_isSign x) (signOf_isSign y) trim1 trim2
        (notzero x la val1) (notzero y lb val2), intOf_signOf x la val1, intOf_signOf y lb val2]
    · obtain ⟨n1, n2, o2, m2⟩ := kept p0 q own
      obtain ⟨o3, m3⟩ := kept3 p0 q o2 n1 n2
      exact ⟨o3, m3.trans m2⟩

/-- `lean_int_big_eq` as a whole: 1 if the two integers are equal, otherwise 0. -/
theorem intBigEq_held {outside : Outside} (heap : Allocator outside) (compares : ComparesSigned heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_eq" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x = y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := intOrder_held heap "lean_int_big_eq" (Expr.eq · 1) (fun v => if v = 1 then 1 else 0) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.eq, h]; rfl) compares fuel a1 a2 x y s after ending good
    first second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.intOrder
  by_cases h1 : x < y
  · have : x ≠ y := by omega
    simp [h1, this]
  · by_cases h2 : x = y
    · simp [h2]
    · simp [h1, h2]

/-- `lean_int_big_le` as a whole: 1 if the first integer is at most the second, otherwise 0. -/
theorem intBigLe_held {outside : Outside} (heap : Allocator outside) (compares : ComparesSigned heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_le" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x ≤ y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := intOrder_held heap "lean_int_big_le" (Expr.ne · 2) (fun v => if v = 2 then 0 else 1) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.ne, h]; rfl) compares fuel a1 a2 x y s after ending good
    first second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.intOrder
  by_cases h1 : x < y
  · have : x ≤ y := by omega
    simp [h1, this]
  · by_cases h2 : x = y
    · simp [h2]
    · have : ¬ x ≤ y := by omega
      simp [h1, h2, this]

/-- `lean_int_big_lt` as a whole: 1 if the first integer is below the second, otherwise 0. -/
theorem intBigLt_held {outside : Outside} (heap : Allocator outside) (compares : ComparesSigned heap)
    (fuel : Nat) (a1 a2 : UInt64) (x y : Int) (s after : State) (ending : Ending)
    (good : heap.good s) (first : IntHeld heap s a1 x) (second : IntHeld heap s a2 y)
    (ran : program.call outside fuel "lean_int_big_lt" [a1, a2] s = .ok (ending, after)) :
    ending = .gave (if x < y then 1 else 0) ∧ heap.good after ∧
      ∀ p0 q, heap.owns s p0 q → heap.owns after p0 q ∧ after.memory q = s.memory q := by
  have h := intOrder_held heap "lean_int_big_lt" (Expr.eq · 0) (fun v => if v = 0 then 1 else 0) rfl
    (fun t l v h => by simp [Expr.run, Op.run, Expr.eq, h]; rfl) compares fuel a1 a2 x y s after ending good
    first second ran
  refine ⟨?_, h.2⟩
  rw [h.1]
  unfold Runtime.Big.intOrder
  by_cases h1 : x < y
  · simp [h1]
  · by_cases h2 : x = y
    · simp [h2]
    · simp [h1, h2]

end Mini.Number
