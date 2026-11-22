import Mini.Run
import Mini.Memory
import Mini.Alloc

/-! # What is proved about the allocator

Statements about the program in `Mini/Alloc.lean` as `Mini/Run.lean` defines its meaning: for every input,
not the ones a test tried. Nothing here runs; no image imports it. -/

namespace Mini.Alloc

/-- A block of a small class holds sixteen bytes for each step of the class, whatever the state, and asking
changes nothing. -/
theorem classBytes_small (outside : Outside) (fuel : Nat) (c : UInt64) (s : State) (h : c < 257) :
    program.call outside (fuel + 4) "class_bytes" [c] s = .ok (.gave (c * 16), s) := by
  simp [Program.call, program, classBytes, listGet, listSet, malloc, free, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, small, smallClasses, first, largeFirst, Expr.lt, Expr.shl, h]
  rfl

/-- The class a small request is given: enough sixteens to hold it. -/
def smallClass (size : UInt64) : UInt64 := (size + 15) / 16

/-- A small request's class is a small class, and its block holds the request with fewer than sixteen bytes
to spare. This is the arithmetic `rt_malloc` does for a request of 1 to 4096 bytes. -/
theorem smallClass_fits (size : UInt64) (low : 1 ≤ size) (high : size ≤ 4096) :
    smallClass size < 257 ∧ size ≤ smallClass size * 16 ∧ smallClass size * 16 < size + 16 := by
  have l : 1 ≤ size.toNat := by simpa [UInt64.le_iff_toNat_le] using low
  have h : size.toNat ≤ 4096 := by simpa [UInt64.le_iff_toNat_le] using high
  have n15 : (15 : UInt64).toNat = 15 := rfl
  have n16 : (16 : UInt64).toNat = 16 := rfl
  have n257 : (257 : UInt64).toNat = 257 := rfl
  have c : (smallClass size).toNat = (size.toNat + 15) / 16 := by
    simp only [smallClass, UInt64.toNat_div, UInt64.toNat_add, n15, n16]
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [UInt64.lt_iff_toNat_lt, c, n257]; omega
  · simp only [UInt64.le_iff_toNat_le, UInt64.toNat_mul, c, n16]; omega
  · simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_mul, UInt64.toNat_add, c, n16]; omega

/-- So a small request is always given a block that holds it: the class `rt_malloc` picks is small, and
`class_bytes` of it, as the program computes it, is at least the size asked for. -/
theorem small_request_fits (outside : Outside) (fuel : Nat) (size : UInt64) (s : State)
    (low : 1 ≤ size) (high : size ≤ 4096) :
    ∃ bytes, program.call outside (fuel + 4) "class_bytes" [smallClass size] s = .ok (.gave bytes, s) ∧ size ≤ bytes :=
  ⟨smallClass size * 16, classBytes_small outside fuel _ s (smallClass_fits size low high).1,
    (smallClass_fits size low high).2.1⟩

/-- A small request when no freed block of its class is waiting and the heap has room: `rt_malloc` does
nothing C leaves open, takes the block from the front of the heap, writes its class and "in use" in the
sixteen bytes before it, and moves the front of the heap past it. Nothing else changes. -/
theorem malloc_fresh (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (lists : Array UInt64)
    (low : 1 ≤ size) (high : size ≤ 4096)
    (hlists : s.arrays "free_small" = some lists)
    (hsize : (smallClass size).toNat < lists.size)
    (hempty : lists[(smallClass size).toNat]'hsize = 0)
    (asked : s.globals "heap_asked" = 1)
    (started : s.globals "heap_at" ≠ 0)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16) :
    program.call outside (fuel + 20) "rt_malloc" [size] s =
      .ok (.gave (s.globals "heap_at" + 16),
        { s with
          globals := put s.globals "heap_at" (s.globals "heap_at" + (16 + smallClass size * 16))
          memory := writeBytes (writeBytes s.memory (s.globals "heap_at") (smallClass size) 8)
            (s.globals "heap_at" + 8) (UInt64.ofNat inUse) 8 }) := by
  have fits := smallClass_fits size low high
  have nz : size ≠ 0 := by intro h; subst h; exact absurd low (by decide)
  have nh : ¬ (4096 : UInt64) < size := by simpa [UInt64.not_lt] using high
  have fold : (size + 15) / 16 = smallClass size := rfl
  have room' : 16 + smallClass size * 16 ≤ s.globals "heap_end" - s.globals "heap_at" := by
    simpa [UInt64.not_lt] using room
  have nc : ¬ (257 : UInt64) ≤ smallClass size := by simpa [UInt64.not_le] using fits.1
  simp [Program.call, program, classBytes, listGet, listSet, malloc, free, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, small, smallClasses, first, largeFirst, largeLast, Expr.lt, Expr.le, Expr.eq, Expr.ne, Expr.shl,
    Expr.shr, Expr.or, outOfMemory, nz, nh, hlists, hsize, hempty, asked, started, room', fold, nc]
  rfl

/-- A block and the second word of its header, eight bytes before it, share no byte. -/
theorem header_apart (block : UInt64) (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8) :
    block + UInt64.ofNat k ≠ block - 16 + 8 + UInt64.ofNat i := by
  intro h
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_ofNat', show (16 : UInt64).toNat = 16 from rfl,
    show (8 : UInt64).toNat = 8 from rfl] at this
  have := block.toNat_lt
  omega

/-- A small request when a freed block of its class is waiting: `rt_malloc` does nothing C leaves open,
hands out that block, takes it off its list (the list now starts at the block it pointed to), clears the
link it held, and marks it in use. Nothing else changes. What it needs of the state is what `rt_free`
leaves: the block's first word is its link, and its header says it is free. -/
theorem malloc_reuse (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (lists : Array UInt64)
    (block link : UInt64) (low : 1 ≤ size) (high : size ≤ 4096)
    (hlists : s.arrays "free_small" = some lists)
    (hsize : (smallClass size).toNat < lists.size)
    (hblock : lists[(smallClass size).toNat]'hsize = block)
    (waiting : block ≠ 0)
    (hlink : readBytes s.memory block 8 = .ok link)
    (hstate : readBytes s.memory (block - 16 + 8) 8 = .ok (UInt64.ofNat freed)) :
    program.call outside (fuel + 20) "rt_malloc" [size] s =
      .ok (.gave (block - 16 + 16),
        { s with
          arrays := put s.arrays "free_small" (some (lists.setIfInBounds (smallClass size).toNat link))
          memory := writeBytes (writeBytes s.memory block 0 8) (block - 16 + 8) (UInt64.ofNat inUse) 8 }) := by
  have fits := smallClass_fits size low high
  have nz : size ≠ 0 := by intro h; subst h; exact absurd low (by decide)
  have nh : ¬ (4096 : UInt64) < size := by simpa [UInt64.not_lt] using high
  have fold : (size + 15) / 16 = smallClass size := rfl
  have nc : ¬ (257 : UInt64) ≤ smallClass size := by simpa [UInt64.not_le] using fits.1
  have hstate' : readBytes (writeBytes s.memory block 0 8) (block - 16 + 8) 8 = .ok (UInt64.ofNat freed) := by
    rw [readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => header_apart block i hi k hk)]; exact hstate
  simp [Program.call, program, classBytes, listGet, listSet, malloc, free, runAll, Stmt.run, Expr.run, Op.run,
    bind, put, small, smallClasses, first, largeFirst, largeLast, Expr.lt, Expr.le, Expr.eq, Expr.ne, Expr.shl,
    Expr.shr, Expr.or, outOfMemory, nz, nh, hlists, hsize, hblock, waiting, hlink, hstate', fold, nc]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put]

/-! ## Freeing: the loop that zeroes a block -/

/-- One turn of a loop: test, and if it holds run the body and go round again with one less to spend. -/
theorem loop_turn (p : Program) (outside : Outside) (fuel : Nat) (condition : Expr) (body : List Stmt)
    (s : State) (locals : Locals) :
    Stmt.run p outside (fuel + 1) (.loop condition body) s locals =
      (do
        if (← condition.run s locals) == 0 then pure (.on, s, locals) else
        match ← runAll p outside fuel body s locals with
        | (.on, s, locals) => Stmt.run p outside fuel (.loop condition body) s locals
        | ended => pure ended) := by
  rw [Stmt.run]
  rfl

/-- Memory with `count` words of zero written from `block + at` up. -/
def zeros (memory : UInt64 → Option UInt8) (block : UInt64) : UInt64 → Nat → UInt64 → Option UInt8
  | _, 0 => memory
  | at_, count + 1 => zeros (writeBytes memory (block + at_) 0 8) block (at_ + 8) count

/-- The loop in `rt_free`, from any point in it: with `count` words still to go it writes exactly those
words as zero, does nothing C leaves open, and leaves every local but its counter as it was. -/
theorem zero_loop (p : Program) (outside : Outside) (block bytes : UInt64) (count : Nat) :
    ∀ (at_ : UInt64) (s : State) (locals : Locals) (extra : Nat),
      locals "at" = some at_ → locals "block" = some block → locals "bytes" = some bytes →
      at_.toNat + 8 * count = bytes.toNat →
      ∃ after, Stmt.run p outside (count + extra + 5)
          (.loop (Expr.lt "at" "bytes") [.store ("block" + "at") 0, .set "at" ("at" + 8)]) s locals =
            .ok (.on, { s with memory := zeros s.memory block at_ count }, after) ∧
          ∀ name, name ≠ "at" → after name = locals name := by
  induction count with
  | zero =>
    intro at_ s locals extra hat hblock hbytes hdone
    have same : at_ = bytes := UInt64.toNat_inj.mp (by omega)
    refine ⟨locals, ?_, fun _ _ => rfl⟩
    simp [Stmt.run, Expr.run, Op.run, Expr.lt, hat, hbytes, same, zeros]
    rfl
  | succ count ih =>
    intro at_ s locals extra hat hblock hbytes hleft
    have less : at_ < bytes := by simp only [UInt64.lt_iff_toNat_lt]; omega
    have room := bytes.toNat_lt
    have next : (at_ + 8).toNat + 8 * count = bytes.toNat := by
      simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
    obtain ⟨after, hrun, hkeep⟩ := ih (at_ + 8) { s with memory := writeBytes s.memory (block + at_) 0 8 }
      (put locals "at" (some (at_ + 8))) extra (by simp [put]) (by simp [put, hblock]) (by simp [put, hbytes]) next
    refine ⟨after, ?_, fun name hname => by rw [hkeep name hname]; simp [put, hname]⟩
    rw [show count + 1 + extra + 5 = (count + extra + 5) + 1 from by omega, loop_turn]
    generalize hround : Stmt.run p outside (count + extra + 5)
      (.loop (Expr.lt "at" "bytes") [.store ("block" + "at") 0, .set "at" ("at" + 8)]) = round at hrun ⊢
    simp [Stmt.run, runAll, Expr.run, Op.run, Expr.lt, hat, hblock, hbytes, less, zeros, hrun]

/-- The zeroing loop under a name of its own, so that a proof can step over it. -/
def zeroLoop (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :=
  Stmt.run p outside fuel (.loop (Expr.lt "at" "bytes") [.store ("block" + "at") 0, .set "at" ("at" + 8)]) s locals

theorem zeroLoop_fold (p : Program) (outside : Outside) (fuel : Nat) (s : State) (locals : Locals) :
    Stmt.run p outside fuel (.loop (.op .lt (.var "at") (.var "bytes"))
      [.store (.op .add (.var "block") (.var "at")) (.lit 0), .set "at" (.op .add (.var "at") (.lit 8))]) s locals =
    zeroLoop p outside fuel s locals := rfl

theorem find_free : program.functions.find? (fun f => f.name == "rt_free") = some free := rfl
theorem find_classBytes : program.functions.find? (fun f => f.name == "class_bytes") = some classBytes := rfl
theorem find_listGet : program.functions.find? (fun f => f.name == "list_get") = some listGet := rfl
theorem find_listSet : program.functions.find? (fun f => f.name == "list_set") = some listSet := rfl

/-- The two words of a block's header share no byte: the state, eight bytes on, and the class. -/
theorem state_apart (header : UInt64) (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8) :
    header + 8 + UInt64.ofNat k ≠ header + UInt64.ofNat i := by
  intro h
  have := congrArg UInt64.toNat h
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat', show (8 : UInt64).toNat = 8 from rfl] at this
  have := header.toNat_lt
  omega

/-- Freeing a block of a small class that is in use: `rt_free` does nothing C leaves open, marks the block
free, writes zero over every byte it held, links it in front of its class's list, and makes it the head of
that list. Nothing else changes. -/
theorem free_small (outside : Outside) (extra : Nat) (block c : UInt64) (s : State) (lists : Array UInt64)
    (hstate : readBytes s.memory (block - 16 + 8) 8 = .ok (UInt64.ofNat inUse))
    (hclass : readBytes s.memory (block - 16) 8 = .ok c)
    (small : c < 257)
    (hlists : s.arrays "free_small" = some lists)
    (hsize : c.toNat < lists.size) :
    program.call outside (c.toNat * 2 + extra + 30) "rt_free" [block] s =
      .ok (.on,
        { s with
          arrays := put s.arrays "free_small" (some (lists.setIfInBounds c.toNat block))
          memory := writeBytes
            (zeros (writeBytes s.memory (block - 16 + 8) (UInt64.ofNat freed) 8) block 0 (c.toNat * 2))
            block (lists[c.toNat]'hsize) 8 }) := by
  have hclass' : readBytes (writeBytes s.memory (block - 16 + 8) (UInt64.ofNat freed) 8) (block - 16) 8 = .ok c := by
    rw [readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => state_apart (block - 16) i hi k hk)]; exact hclass
  have nc : ¬ (257 : UInt64) ≤ c := by simpa [UInt64.not_le] using small
  have csmall : c.toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using small
  have bytes : (0 : UInt64).toNat + 8 * (c.toNat * 2) = (c * 16).toNat := by
    simp only [UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl, show (0 : UInt64).toNat = 0 from rfl]; omega
  obtain ⟨after, hrun, hkeep⟩ := zero_loop program outside block (c * 16) (c.toNat * 2) 0
    { s with memory := writeBytes s.memory (block - 16 + 8) (UInt64.ofNat freed) 8 }
    (put (put (put (put (put (fun _ => none) "block" (some block)) "header" (some (block - 16))) "size_class" (some c))
      "bytes" (some (c * 16))) "at" (some 0))
    (extra + 18) (by simp [put]) (by simp [put]) (by simp [put]) bytes
  have hrun' : zeroLoop program outside (c.toNat * 2 + extra + 23)
      { s with memory := writeBytes s.memory (block - 16 + 8) (UInt64.ofNat freed) 8 }
      (put (put (put (put (put (fun _ => none) "block" (some block)) "header" (some (block - 16))) "size_class" (some c))
        "bytes" (some (c * 16))) "at" (some 0)) =
      .ok (.on, (⟨s.globals, s.arrays,
        zeros (writeBytes s.memory (block - 16 + 8) (UInt64.ofNat freed) 8) block 0 (c.toNat * 2)⟩ : State),
        after) := by
    rw [show c.toNat * 2 + extra + 23 = c.toNat * 2 + (extra + 18) + 5 from by omega]; exact hrun
  have kclass := hkeep "size_class" (by decide)
  have kblock := hkeep "block" (by decide)
  simp [put] at kclass kblock
  simp [Program.call, find_free, find_classBytes, find_listGet, find_listSet, classBytes, listGet, listSet, free,
    runAll, Stmt.run, Expr.run, Op.run, bind, put, Mini.Alloc.small, smallClasses, Expr.lt, Expr.ne, hstate,
    ↓zeroLoop_fold]
  simp [Bind.bind, Except.bind, Pure.pure, Except.pure, Functor.map, Except.map, put, hclass', nc, hrun', kclass,
    kblock, hlists, hsize]

end Mini.Alloc
