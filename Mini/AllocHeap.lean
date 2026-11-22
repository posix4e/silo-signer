import Mini.AllocProofs

/-! # A heap that is in order

The theorems in `Mini/AllocProofs.lean` say what one call does to a state. This says what a state has to be
for calls to go on being safe, and shows that a call leaves it that way: the blocks handed out so far lie
one after another from where the heap began, each behind sixteen bytes that hold its class and whether it
is in use, and none of them shares a byte with another. -/

namespace Mini.Alloc

/-- A block that has been handed out at some time: where it is and the class it was cut for. -/
structure Block where
  address : UInt64
  size_class : UInt64

/-- How many bytes a block of a small class holds. -/
def Block.bytes (b : Block) : Nat := b.size_class.toNat * 16

/-- The blocks lie one after another from byte `start` to byte `finish`, each behind its header, and the
header of each says its class and one of the two states. -/
def Laid (memory : UInt64 → Option UInt8) : Nat → List Block → Nat → Prop
  | start, [], finish => start = finish
  | start, b :: rest, finish =>
    b.address.toNat = start + 16 ∧ 1 ≤ b.size_class.toNat ∧ b.size_class.toNat < 257 ∧
    readBytes memory (b.address - 16) 8 = .ok b.size_class ∧
    (readBytes memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat inUse) ∨
      readBytes memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat freed)) ∧
    Laid memory (start + 16 + b.bytes) rest finish

theorem Laid.le {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) : start ≤ finish := by
  induction blocks generalizing start with
  | nil => exact Nat.le_of_eq h
  | cons b rest ih => have := ih h.2.2.2.2.2; omega

/-- A word written at or after byte `to` shares no byte with a word that ends at or before it. -/
theorem below_apart (x start : UInt64) (h : x.toNat + 8 ≤ start.toNat) (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8)
    (room : start.toNat + 8 ≤ 18446744073709551616) : start + UInt64.ofNat k ≠ x + UInt64.ofNat i := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  omega

/-- Writing a word beyond the last block leaves the blocks as they were. -/
theorem Laid.frame {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (at_ word : UInt64) (beyond : finish ≤ at_.toNat)
    (room : at_.toNat + 8 ≤ 18446744073709551616) :
    Laid (writeBytes memory at_ word 8) start blocks finish := by
  induction blocks generalizing start with
  | nil => exact h
  | cons b rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    have header : (b.address - 16).toNat = start := by
      simp only [UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl]; have := b.address.toNat_lt; omega
    have second : (b.address - 16 + 8).toNat = start + 8 := by
      simp only [UInt64.toNat_add, header, show (8 : UInt64).toNat = 8 from rfl]; have := b.address.toNat_lt; omega
    have keep1 : readBytes (writeBytes memory at_ word 8) (b.address - 16) 8 = readBytes memory (b.address - 16) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by simp only [Block.bytes] at order; omega) i hi k hk room)
    have keep2 : readBytes (writeBytes memory at_ word 8) (b.address - 16 + 8) 8 =
        readBytes memory (b.address - 16 + 8) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by simp only [Block.bytes] at order; omega) i hi k hk room)
    exact ⟨where_, low, high, by rw [keep1]; exact hclass, by rw [keep2]; exact hstate, ih hrest⟩

/-- One more block on the end. -/
theorem Laid.append {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (last : Laid memory finish [b] (finish + 16 + b.bytes)) :
    Laid memory start (blocks ++ [b]) (finish + 16 + b.bytes) := by
  induction blocks generalizing start with
  | nil => rw [show start = finish from h]; exact last
  | cons first rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    exact ⟨where_, low, high, hclass, hstate, ih hrest⟩

/-- A word shares no byte with one that begins at or after its end. -/
theorem above_apart (x start : UInt64) (h : start.toNat + 8 ≤ x.toNat) (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8)
    (room : x.toNat + 8 ≤ 18446744073709551616) : start + UInt64.ofNat k ≠ x + UInt64.ofNat i := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  omega

/-- Writing a word that ends before the first block leaves the blocks as they were. -/
theorem Laid.frame_below {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (at_ word : UInt64) (before : at_.toNat + 8 ≤ start)
    (top : finish ≤ 18446744073709551616) :
    Laid (writeBytes memory at_ word 8) start blocks finish := by
  induction blocks generalizing start with
  | nil => exact h
  | cons b rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    simp only [Block.bytes] at order
    have header : (b.address - 16).toNat = start := by
      simp only [UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl]; have := b.address.toNat_lt; omega
    have second : (b.address - 16 + 8).toNat = start + 8 := by
      simp only [UInt64.toNat_add, header, show (8 : UInt64).toNat = 8 from rfl]; have := b.address.toNat_lt; omega
    have keep1 : readBytes (writeBytes memory at_ word 8) (b.address - 16) 8 = readBytes memory (b.address - 16) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => above_apart _ _ (by omega) i hi k hk (by omega))
    have keep2 : readBytes (writeBytes memory at_ word 8) (b.address - 16 + 8) 8 =
        readBytes memory (b.address - 16 + 8) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => above_apart _ _ (by omega) i hi k hk (by omega))
    exact ⟨where_, low, high, by rw [keep1]; exact hclass, by rw [keep2]; exact hstate,
      ih hrest (by simp only [Block.bytes]; omega)⟩

/-- Every block lies inside the stretch the blocks are laid over, behind its header. -/
theorem Laid.inside {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (member : b ∈ blocks) :
    start + 16 ≤ b.address.toNat ∧ b.address.toNat + b.bytes ≤ finish := by
  induction blocks generalizing start with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨by omega, by omega⟩
    · have := ih hrest later
      simp only [Block.bytes] at this ⊢
      omega

/-- Writing a word inside a block, where the block's own bytes are, leaves every header as it was: so the
blocks stay laid as they were whatever a block's holder writes in it. -/
theorem Laid.frame_body {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (member : b ∈ blocks) (at_ word : UInt64)
    (low : b.address.toNat ≤ at_.toNat) (high : at_.toNat + 8 ≤ b.address.toNat + b.bytes)
    (top : finish ≤ 18446744073709551616) :
    Laid (writeBytes memory at_ word 8) start blocks finish := by
  induction blocks generalizing start with
  | nil => cases member
  | cons first rest ih =>
    have whole := h
    obtain ⟨where_, flow, fhigh, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    have place := whole.inside b member
    simp only [Block.bytes] at order place high
    have header : (first.address - 16).toNat = start := by
      simp only [UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl]; have := first.address.toNat_lt; omega
    have second : (first.address - 16 + 8).toNat = start + 8 := by
      simp only [UInt64.toNat_add, header, show (8 : UInt64).toNat = 8 from rfl]
      have := first.address.toNat_lt; omega
    have keep1 : readBytes (writeBytes memory at_ word 8) (first.address - 16) 8 =
        readBytes memory (first.address - 16) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk (by omega))
    have keep2 : readBytes (writeBytes memory at_ word 8) (first.address - 16 + 8) 8 =
        readBytes memory (first.address - 16 + 8) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk (by omega))
    refine ⟨where_, flow, fhigh, by rw [keep1]; exact hclass, by rw [keep2]; exact hstate, ?_⟩
    rcases List.mem_cons.mp member with rfl | later
    · exact hrest.frame_below at_ word (by simp only [Block.bytes]; omega) top
    · exact ih hrest later

/-- Marking one block as in use or as free, by writing the second word of its header, leaves the blocks
laid as they were: its header still says one of the two states, and no other header is touched. -/
theorem Laid.mark {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (member : b ∈ blocks) (state : UInt64)
    (one : state = UInt64.ofNat inUse ∨ state = UInt64.ofNat freed) (top : finish ≤ 18446744073709551616) :
    Laid (writeBytes memory (b.address - 16 + 8) state 8) start blocks finish := by
  induction blocks generalizing start with
  | nil => cases member
  | cons first rest ih =>
    have whole := h
    obtain ⟨where_, flow, fhigh, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    have place := whole.inside b member
    simp only [Block.bytes] at order place
    have header : (first.address - 16).toNat = start := by
      simp only [UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl]; have := first.address.toNat_lt; omega
    have second : (first.address - 16 + 8).toNat = start + 8 := by
      simp only [UInt64.toNat_add, header, show (8 : UInt64).toNat = 8 from rfl]
      have := first.address.toNat_lt; omega
    have written : (b.address - 16 + 8).toNat = b.address.toNat - 8 := by
      simp only [UInt64.toNat_add, UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl,
        show (8 : UInt64).toNat = 8 from rfl]
      have := b.address.toNat_lt; omega
    rcases List.mem_cons.mp member with rfl | later
    · -- The block marked is the first: its class word is below the write, its state word is the write.
      have keep1 : readBytes (writeBytes memory (b.address - 16 + 8) state 8) (b.address - 16) 8 =
          readBytes memory (b.address - 16) 8 :=
        readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => state_apart _ i hi k hk)
      refine ⟨where_, flow, fhigh, by rw [keep1]; exact hclass, ?_, ?_⟩
      · rw [readBytes_writeBytes_word]
        rcases one with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · exact hrest.frame_below _ state (by simp only [Block.bytes]; omega) top
    · -- The block marked is a later one: the first block's header ends before the write begins.
      have further := hrest.inside b later
      simp only [Block.bytes] at further
      have keep1 : readBytes (writeBytes memory (b.address - 16 + 8) state 8) (first.address - 16) 8 =
          readBytes memory (first.address - 16) 8 :=
        readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk (by omega))
      have keep2 : readBytes (writeBytes memory (b.address - 16 + 8) state 8) (first.address - 16 + 8) 8 =
          readBytes memory (first.address - 16 + 8) 8 :=
        readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk (by omega))
      exact ⟨where_, flow, fhigh, by rw [keep1]; exact hclass, by rw [keep2]; exact hstate, ih hrest later⟩

/-- Writing zero over words of a block, as `rt_free` does, leaves the blocks laid as they were. -/
theorem Laid.zeros {start finish : Nat} {blocks : List Block} (b : Block) (member : b ∈ blocks)
    (top : finish ≤ 18446744073709551616) (count : Nat) :
    ∀ (memory : UInt64 → Option UInt8) (at_ : UInt64), Laid memory start blocks finish →
      at_.toNat + 8 * count ≤ b.bytes →
      Laid (Mini.Alloc.zeros memory b.address at_ count) start blocks finish := by
  induction count with
  | zero => intro memory at_ h _; exact h
  | succ count ih =>
    intro memory at_ h fits
    have place := h.inside b member
    simp only [Block.bytes] at place fits
    have here : (b.address + at_).toNat = b.address.toNat + at_.toNat := by
      rw [UInt64.toNat_add]; omega
    have next : (at_ + 8).toNat = at_.toNat + 8 := by
      simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
    exact ih _ (at_ + 8)
      (h.frame_body b member (b.address + at_) 0 (by omega) (by simp only [Block.bytes]; omega) top)
      (by simp only [Block.bytes]; omega)

/-- A heap in order: the blocks handed out so far are laid from `base` to the front of the heap, and the
front has not passed the end. -/
def InOrder (s : State) (base : Nat) (blocks : List Block) : Prop :=
  Laid s.memory base blocks (s.globals "heap_at").toNat ∧
    (s.globals "heap_at").toNat ≤ (s.globals "heap_end").toNat

/-- The state `malloc_fresh` shows `rt_malloc` leaves. -/
def afterFresh (s : State) (size : UInt64) : State :=
  { s with
    globals := put s.globals "heap_at" (s.globals "heap_at" + (16 + smallClass size * 16))
    memory := writeBytes (writeBytes s.memory (s.globals "heap_at") (smallClass size) 8)
      (s.globals "heap_at" + 8) (UInt64.ofNat inUse) 8 }

/-- Taking a block from fresh heap keeps the heap in order, with that block added after the others. So it
shares no byte with any block handed out before, and every header written before is as it was. -/
theorem fresh_keeps (s : State) (base : Nat) (blocks : List Block) (size : UInt64)
    (low : 1 ≤ size) (high : size ≤ 4096) (order : InOrder s base blocks)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16) :
    InOrder (afterFresh s size) base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) := by
  obtain ⟨laid, within⟩ := order
  have fits := smallClass_fits size low high
  have csmall : (smallClass size).toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using fits.1
  have sized : 1 ≤ size.toNat := by simpa [UInt64.le_iff_toNat_le] using low
  have cpos : 1 ≤ (smallClass size).toNat := by
    have := fits.2.1
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl] at this
    omega
  have need : (16 + smallClass size * 16).toNat = 16 + (smallClass size).toNat * 16 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl]; omega
  have fitsHeap : (s.globals "heap_at").toNat + 16 + (smallClass size).toNat * 16 ≤ (s.globals "heap_end").toNat := by
    have := room
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using within),
      need] at this
    omega
  have top := (s.globals "heap_end").toNat_lt
  have front : (s.globals "heap_at" + (16 + smallClass size * 16)).toNat =
      (s.globals "heap_at").toNat + 16 + (smallClass size).toNat * 16 := by
    rw [UInt64.toNat_add, need]; omega
  have second : (s.globals "heap_at" + 8).toNat = (s.globals "heap_at").toNat + 8 := by
    simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
  have address : (s.globals "heap_at" + 16).toNat = (s.globals "heap_at").toNat + 16 := by
    simp only [UInt64.toNat_add, show (16 : UInt64).toNat = 16 from rfl]; omega
  have back : s.globals "heap_at" + 16 - 16 = s.globals "heap_at" := UInt64.add_sub_cancel _ _
  refine ⟨?_, ?_⟩
  · simp only [afterFresh, put, ↓reduceIte, front]
    have kept := (laid.frame (s.globals "heap_at") (smallClass size) (Nat.le_refl _) (by omega)).frame
      (s.globals "heap_at" + 8) (UInt64.ofNat inUse) (by omega) (by omega)
    refine kept.append ⟨s.globals "heap_at" + 16, smallClass size⟩ ⟨address, cpos, csmall, ?_, Or.inl ?_, rfl⟩
    · show readBytes _ (s.globals "heap_at" + 16 - 16) 8 = _
      rw [back, readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => state_apart _ i hi k hk)]
      exact readBytes_writeBytes_word _ _ _
    · show readBytes _ (s.globals "heap_at" + 16 - 16 + 8) 8 = _
      rw [back]
      exact readBytes_writeBytes_word _ _ _
  · simp only [afterFresh, put, ↓reduceIte, front]
    have : (if "heap_end" = "heap_at" then s.globals "heap_at" + (16 + smallClass size * 16)
        else s.globals "heap_end") = s.globals "heap_end" := by simp
    simpa [this] using fitsHeap

/-- The two together, about the program itself: on a heap in order, a small request served from fresh heap
does nothing C leaves open, returns a block, and leaves the heap in order with that block added. -/
theorem malloc_fresh_in_order (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (lists : Array UInt64)
    (base : Nat) (blocks : List Block) (low : 1 ≤ size) (high : size ≤ 4096)
    (hlists : s.arrays "free_small" = some lists)
    (hsize : (smallClass size).toNat < lists.size)
    (hempty : lists[(smallClass size).toNat]'hsize = 0)
    (asked : s.globals "heap_asked" = 1)
    (started : s.globals "heap_at" ≠ 0)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16)
    (order : InOrder s base blocks) :
    ∃ after, program.call outside (fuel + 20) "rt_malloc" [size] s = .ok (.gave (s.globals "heap_at" + 16), after) ∧
      InOrder after base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) :=
  ⟨afterFresh s size, malloc_fresh outside fuel size s lists low high hlists hsize hempty asked started room,
    fresh_keeps s base blocks size low high order room⟩

/-- What the header of a block that was handed out says: its class, which is a small one. -/
theorem Laid.header {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (member : b ∈ blocks) :
    readBytes memory (b.address - 16) 8 = .ok b.size_class ∧ 1 ≤ b.size_class.toNat ∧ b.size_class.toNat < 257 := by
  induction blocks generalizing start with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨_, low, high, hclass, _, hrest⟩ := h
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨hclass, low, high⟩
    · exact ih hrest later

/-- Freeing a block that was handed out and is in use keeps the heap in order: the same blocks, laid as
they were. Its bytes are zeroed and its first word becomes a link, and no other block's header changes. -/
theorem free_keeps (s : State) (base : Nat) (blocks : List Block) (b : Block) (member : b ∈ blocks)
    (next : UInt64) (lists : Array UInt64) (order : InOrder s base blocks) :
    InOrder
      { s with
        arrays := put s.arrays "free_small" (some (lists.setIfInBounds b.size_class.toNat b.address))
        memory := writeBytes
          (zeros (writeBytes s.memory (b.address - 16 + 8) (UInt64.ofNat freed) 8) b.address 0
            (b.size_class.toNat * 2))
          b.address next 8 }
      base blocks := by
  obtain ⟨laid, within⟩ := order
  have top : (s.globals "heap_at").toNat ≤ 18446744073709551616 := by
    have := (s.globals "heap_end").toNat_lt; omega
  have sized := (laid.header b member).2.1
  have marked := laid.mark b member (UInt64.ofNat freed) (Or.inr rfl) top
  have wiped := Laid.zeros b member top (b.size_class.toNat * 2) _ 0 marked
    (by simp only [Block.bytes, show (0 : UInt64).toNat = 0 from rfl]; omega)
  exact ⟨wiped.frame_body b member b.address next (Nat.le_refl _) (by simp only [Block.bytes]; omega) top, within⟩

/-- Handing out again a block that was handed out before keeps the heap in order: the same blocks, laid as
they were. Its link is cleared and it is marked in use, and no other block's header changes. -/
theorem reuse_keeps (s : State) (base : Nat) (blocks : List Block) (b : Block) (member : b ∈ blocks)
    (link : UInt64) (lists : Array UInt64) (index : Nat) (order : InOrder s base blocks) :
    InOrder
      { s with
        arrays := put s.arrays "free_small" (some (lists.setIfInBounds index link))
        memory := writeBytes (writeBytes s.memory b.address 0 8) (b.address - 16 + 8) (UInt64.ofNat inUse) 8 }
      base blocks := by
  obtain ⟨laid, within⟩ := order
  have top : (s.globals "heap_at").toNat ≤ 18446744073709551616 := by
    have := (s.globals "heap_end").toNat_lt; omega
  have sized := (laid.header b member).2.1
  have cleared := laid.frame_body b member b.address 0 (Nat.le_refl _) (by simp only [Block.bytes]; omega) top
  exact ⟨cleared.mark b member (UInt64.ofNat inUse) (Or.inl rfl) top, within⟩

/-- About the program itself: freeing a block that was handed out, of a small class and in use, does nothing
C leaves open and leaves the heap in order. -/
theorem free_small_in_order (outside : Outside) (extra : Nat) (s : State) (lists : Array UInt64) (base : Nat)
    (blocks : List Block) (b : Block) (member : b ∈ blocks) (order : InOrder s base blocks)
    (live : readBytes s.memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat inUse))
    (hlists : s.arrays "free_small" = some lists)
    (hsize : b.size_class.toNat < lists.size) :
    ∃ after, program.call outside (b.size_class.toNat * 2 + extra + 30) "rt_free" [b.address] s = .ok (.on, after) ∧
      InOrder after base blocks := by
  have head := order.1.header b member
  have small : b.size_class < 257 := by
    simp only [UInt64.lt_iff_toNat_lt, show (257 : UInt64).toNat = 257 from rfl]; exact head.2.2
  exact ⟨_, free_small outside extra b.address b.size_class s lists live head.1 small hlists hsize,
    free_keeps s base blocks b member _ lists order⟩

/-! ## The lists of freed blocks -/

/-- Of two blocks that were handed out, the one at the lower address ends, bytes and all, before the header
of the other begins. So no two of them share a byte, headers included. -/
theorem Laid.separate {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (lower upper : Block) (m1 : lower ∈ blocks) (m2 : upper ∈ blocks)
    (order : lower.address.toNat < upper.address.toNat) :
    lower.address.toNat + lower.bytes + 16 ≤ upper.address.toNat := by
  induction blocks generalizing start with
  | nil => cases m1
  | cons first rest ih =>
    obtain ⟨where_, _, _, _, _, hrest⟩ := h
    rcases List.mem_cons.mp m1 with rfl | later1 <;> rcases List.mem_cons.mp m2 with rfl | later2
    · omega
    · have := hrest.inside upper later2; omega
    · have := hrest.inside lower later1; omega
    · exact ih hrest later1 later2

/-- A list of freed blocks: `head` is the first address in `addresses`, the first word of each block is the
address of the next, and the last one's is zero. -/
def Chain (memory : UInt64 → Option UInt8) : UInt64 → List UInt64 → Prop
  | head, [] => head = 0
  | head, a :: rest => head = a ∧ a ≠ 0 ∧ ∃ link, readBytes memory a 8 = .ok link ∧ Chain memory link rest

/-- A word that shares no byte with the first word of any block on a list can be written without changing
the list. -/
theorem Chain.frame {memory : UInt64 → Option UInt8} {head : UInt64} {addresses : List UInt64}
    (h : Chain memory head addresses) (at_ word : UInt64)
    (apart : ∀ a, a ∈ addresses → (at_.toNat + 8 ≤ a.toNat ∧ a.toNat + 8 ≤ 18446744073709551616) ∨
      (a.toNat + 8 ≤ at_.toNat ∧ at_.toNat + 8 ≤ 18446744073709551616)) :
    Chain (writeBytes memory at_ word 8) head addresses := by
  induction addresses generalizing head with
  | nil => exact h
  | cons a rest ih =>
    obtain ⟨same, nonzero, link, hlink, hrest⟩ := h
    have keep : readBytes (writeBytes memory at_ word 8) a 8 = readBytes memory a 8 := by
      rcases apart a (List.mem_cons_self) with ⟨before, room⟩ | ⟨after, room⟩
      · exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => above_apart _ _ before i hi k hk room)
      · exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ after i hi k hk room)
    exact ⟨same, nonzero, link, by rw [keep]; exact hlink,
      ih hrest (fun x hx => apart x (List.mem_cons_of_mem _ hx))⟩

/-- The list of freed blocks of one class is what it should be: a chain from the head the allocator keeps
for the class, with no block on it twice, and every block on it one that was handed out, of that class, whose
header says it is free. -/
def ListFor (memory : UInt64 → Option UInt8) (blocks : List Block) (head : UInt64) (size_class : Nat)
    (addresses : List UInt64) : Prop :=
  Chain memory head addresses ∧ addresses.Nodup ∧
    ∀ a, a ∈ addresses → ∃ b, b ∈ blocks ∧ b.address = a ∧ b.size_class.toNat = size_class ∧
      readBytes memory (a - 16 + 8) 8 = .ok (UInt64.ofNat freed)

/-- A word written clear of the sixteen bytes around each listed block's address (the second word of its
header and its own first word) leaves the list as it was. -/
theorem ListFor.frame {memory : UInt64 → Option UInt8} {blocks : List Block} {head : UInt64} {size_class : Nat}
    {addresses : List UInt64} (h : ListFor memory blocks head size_class addresses) (at_ word : UInt64)
    (room : at_.toNat + 8 ≤ 18446744073709551616)
    (clear : ∀ a, a ∈ addresses → 16 ≤ a.toNat ∧ a.toNat + 8 ≤ 18446744073709551616 ∧
      (at_.toNat + 8 ≤ a.toNat - 8 ∨ a.toNat + 8 ≤ at_.toNat)) :
    ListFor (writeBytes memory at_ word 8) blocks head size_class addresses := by
  obtain ⟨chain, distinct, each⟩ := h
  refine ⟨chain.frame at_ word (fun a ha => ?_), distinct, fun a ha => ?_⟩
  · obtain ⟨_, top, side⟩ := clear a ha
    rcases side with before | after
    · exact Or.inl ⟨by omega, top⟩
    · exact Or.inr ⟨after, room⟩
  · obtain ⟨b, member, where_, cls, state⟩ := each a ha
    obtain ⟨low, top, side⟩ := clear a ha
    have second : (a - 16 + 8).toNat = a.toNat - 8 := by
      simp only [UInt64.toNat_add, UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl,
        show (8 : UInt64).toNat = 8 from rfl]
      have := a.toNat_lt; omega
    have keep : readBytes (writeBytes memory at_ word 8) (a - 16 + 8) 8 = readBytes memory (a - 16 + 8) 8 := by
      rcases side with before | after
      · exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => above_apart _ _ (by omega) i hi k hk (by omega))
      · exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk room)
    exact ⟨b, member, where_, cls, by rw [keep]; exact state⟩

/-- A heap that is sound: in order, and with every class's list of freed blocks what it should be. -/
def Sound (s : State) (base : Nat) (blocks : List Block) : Prop :=
  InOrder s base blocks ∧
    ∃ lists, s.arrays "free_small" = some lists ∧ lists.size = 257 ∧
      ∀ c, c < 257 → ∃ addresses, ListFor s.memory blocks (lists.getD c 0) c addresses

/-- Taking a block from fresh heap keeps the heap sound. -/
theorem fresh_sound (s : State) (base : Nat) (blocks : List Block) (size : UInt64)
    (low : 1 ≤ size) (high : size ≤ 4096) (sound : Sound s base blocks)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16) :
    Sound (afterFresh s size) base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) := by
  obtain ⟨order, lists, hlists, hsize, each⟩ := sound
  refine ⟨fresh_keeps s base blocks size low high order room, lists, hlists, hsize, fun c hc => ?_⟩
  obtain ⟨addresses, listed⟩ := each c hc
  obtain ⟨laid, within⟩ := order
  have top := (s.globals "heap_end").toNat_lt
  have fits := smallClass_fits size low high
  have csmall : (smallClass size).toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using fits.1
  have need : (16 + smallClass size * 16).toNat = 16 + (smallClass size).toNat * 16 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl]; omega
  have fitsHeap : (s.globals "heap_at").toNat + 16 + (smallClass size).toNat * 16 ≤ (s.globals "heap_end").toNat := by
    have := room
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using within),
      need] at this
    omega
  have second : (s.globals "heap_at" + 8).toNat = (s.globals "heap_at").toNat + 8 := by
    simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
  -- Every listed block lies below the front of the heap, where both words are written.
  have below : ∀ a, a ∈ addresses → 16 ≤ a.toNat ∧ a.toNat + 16 ≤ (s.globals "heap_at").toNat := by
    intro a ha
    obtain ⟨b, member, where_, _, _⟩ := listed.2.2 a ha
    have place := laid.inside b member
    have sized := (laid.header b member).2.1
    simp only [Block.bytes] at place
    rw [← where_]; omega
  have first := listed.frame (s.globals "heap_at") (smallClass size) (by omega)
    (fun a ha => ⟨(below a ha).1, by have := (below a ha).2; omega, Or.inr (by have := (below a ha).2; omega)⟩)
  have both := first.frame (s.globals "heap_at" + 8) (UInt64.ofNat inUse) (by omega)
    (fun a ha => ⟨(below a ha).1, by have := (below a ha).2; omega, Or.inr (by have := (below a ha).2; omega)⟩)
  obtain ⟨chain, distinct, members⟩ := both
  exact ⟨addresses, chain, distinct, fun a ha => by
    obtain ⟨b, member, rest⟩ := members a ha
    exact ⟨b, List.mem_append_left _ member, rest⟩⟩

/-- Where another block that was handed out lies, seen from one of them: at least a header below it, or
past its last byte and a header. -/
theorem Laid.clear {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (top : finish ≤ 18446744073709551616) (b0 : Block) (m0 : b0 ∈ blocks)
    (b : Block) (m : b ∈ blocks) (other : b.address ≠ b0.address) :
    16 ≤ b.address.toNat ∧ b.address.toNat + 16 ≤ 18446744073709551616 ∧ 16 ≤ b0.address.toNat ∧ 16 ≤ b0.bytes ∧
      (b.address.toNat + 32 ≤ b0.address.toNat ∨ b0.address.toNat + b0.bytes + 16 ≤ b.address.toNat) := by
  have p := h.inside b m
  have p0 := h.inside b0 m0
  have s := (h.header b m).2.1
  have s0 := (h.header b0 m0).2.1
  have differ : b.address.toNat ≠ b0.address.toNat := fun e => other (UInt64.toNat_inj.mp e)
  simp only [Block.bytes] at p p0 ⊢
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  rcases Nat.lt_or_gt_of_ne differ with lt | gt
  · have := h.separate b b0 m m0 lt; simp only [Block.bytes] at this; omega
  · have := h.separate b0 b m0 m gt; simp only [Block.bytes] at this; omega

/-- Two blocks that were handed out at the same address are of the same class: their header says so. -/
theorem Laid.same_class {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b1 b2 : Block) (m1 : b1 ∈ blocks) (m2 : b2 ∈ blocks)
    (same : b1.address = b2.address) : b1.size_class = b2.size_class := by
  have r1 := (h.header b1 m1).1
  have r2 := (h.header b2 m2).1
  rw [same, r2] at r1
  exact (Except.ok.inj r1).symm

/-- A list none of whose blocks is at `b0`'s address is unchanged by clearing `b0`'s first word and by
writing its state. -/
theorem ListFor.around {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    {head : UInt64} {size_class : Nat} {addresses : List UInt64}
    (h : ListFor memory blocks head size_class addresses) (laid : Laid memory start blocks finish)
    (top : finish ≤ 18446744073709551616) (b0 : Block) (m0 : b0 ∈ blocks)
    (away : ∀ a, a ∈ addresses → a ≠ b0.address) (word state : UInt64) :
    ListFor (writeBytes (writeBytes memory b0.address word 8) (b0.address - 16 + 8) state 8) blocks head size_class
      addresses := by
  have place : ∀ a, a ∈ addresses → 16 ≤ a.toNat ∧ a.toNat + 16 ≤ 18446744073709551616 ∧ 16 ≤ b0.address.toNat ∧
      16 ≤ b0.bytes ∧ (a.toNat + 32 ≤ b0.address.toNat ∨ b0.address.toNat + b0.bytes + 16 ≤ a.toNat) := by
    intro a ha
    obtain ⟨b, member, where_, _, _⟩ := h.2.2 a ha
    have := laid.clear top b0 m0 b member (by rw [where_]; exact away a ha)
    rwa [where_] at this
  have inside := laid.inside b0 m0
  have sized0 := (laid.header b0 m0).2.1
  simp only [Block.bytes] at inside
  have written : (b0.address - 16 + 8).toNat = b0.address.toNat - 8 := by
    simp only [UInt64.toNat_add, UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    have := b0.address.toNat_lt; omega
  have first := h.frame b0.address word (by omega) (fun a ha => by
    obtain ⟨l, t, l0, s0, side⟩ := place a ha
    exact ⟨l, by omega, by omega⟩)
  exact first.frame (b0.address - 16 + 8) state (by rw [written]; omega) (fun a ha => by
    obtain ⟨l, t, l0, s0, side⟩ := place a ha
    rw [written]
    exact ⟨l, by omega, by omega⟩)

/-- On a sound heap, a class whose list is not empty has at its head a block that was handed out and is
free, with its link in its first word: exactly what `malloc_reuse` asks for. And the state that theorem
leaves, with the block taken off its list and marked in use, is sound again. -/
theorem reuse_sound (s : State) (base : Nat) (blocks : List Block) (lists : Array UInt64) (c0 : Nat)
    (hc0 : c0 < 257) (sound : Sound s base blocks) (hlists : s.arrays "free_small" = some lists)
    (waiting : lists.getD c0 0 ≠ 0) :
    ∃ b0 link, b0 ∈ blocks ∧ b0.address = lists.getD c0 0 ∧ b0.size_class.toNat = c0 ∧
      readBytes s.memory b0.address 8 = .ok link ∧
      readBytes s.memory (b0.address - 16 + 8) 8 = .ok (UInt64.ofNat freed) ∧
      Sound
        { s with
          arrays := put s.arrays "free_small" (some (lists.setIfInBounds c0 link))
          memory := writeBytes (writeBytes s.memory b0.address 0 8) (b0.address - 16 + 8) (UInt64.ofNat inUse) 8 }
        base blocks := by
  obtain ⟨order, lists', hlists', hsize, each⟩ := sound
  have same : lists' = lists := Option.some.inj (hlists'.symm.trans hlists)
  subst same
  have top : (s.globals "heap_at").toNat ≤ 18446744073709551616 := by
    have := (s.globals "heap_end").toNat_lt; have := order.2; omega
  obtain ⟨addresses, chain, distinct, members⟩ := each c0 hc0
  cases addresses with
  | nil => exact absurd chain waiting
  | cons a0 rest =>
    obtain ⟨head, _, link, hlink, chainRest⟩ := chain
    obtain ⟨b0, m0, where0, class0, state0⟩ := members a0 List.mem_cons_self
    have fresh := List.nodup_cons.mp distinct
    refine ⟨b0, link, m0, by rw [where0, head], class0, by rw [where0]; exact hlink, by rw [where0]; exact state0,
      reuse_keeps s base blocks b0 m0 link lists' c0 order, lists'.setIfInBounds c0 link, by simp [put], by simpa using hsize,
      fun c hc => ?_⟩
    by_cases hsame : c = c0
    · subst hsame
      have listed : ListFor s.memory blocks link c rest :=
        ⟨chainRest, fresh.2, fun a ha => members a (List.mem_cons_of_mem _ ha)⟩
      have moved := listed.around order.1 top b0 m0
        (fun a ha e => fresh.1 (by rw [← where0, ← e]; exact ha)) 0 (UInt64.ofNat inUse)
      refine ⟨rest, ?_⟩
      have at_head : (lists'.setIfInBounds c link).getD c 0 = link := by
        simp [Array.getD_eq_getD_getElem?, hsize, hc]
      rw [at_head]; exact moved
    · obtain ⟨others, listed⟩ := each c hc
      have moved := listed.around order.1 top b0 m0 (fun a ha e => by
        obtain ⟨b, member, where_, cls, _⟩ := listed.2.2 a ha
        have classes := order.1.same_class b b0 member m0 (by rw [where_, e])
        exact hsame (by rw [← cls, ← class0, classes])) 0 (UInt64.ofNat inUse)
      refine ⟨others, ?_⟩
      have elsewhere : (lists'.setIfInBounds c0 link).getD c 0 = lists'.getD c 0 := by
        simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hsame)]
      rw [elsewhere]; exact moved

/-- Zeroing words of a block leaves a word that ends at or before the block as it was. -/
theorem zeros_below (block x : UInt64) (count : Nat) :
    ∀ (memory : UInt64 → Option UInt8) (at_ : UInt64), x.toNat + 8 ≤ block.toNat →
      block.toNat + at_.toNat + 8 * count ≤ 18446744073709551616 →
      readBytes (zeros memory block at_ count) x 8 = readBytes memory x 8 := by
  induction count with
  | zero => intro memory at_ _ _; rfl
  | succ count ih =>
    intro memory at_ below room
    have here : (block + at_).toNat = block.toNat + at_.toNat := by rw [UInt64.toNat_add]; omega
    have next : (at_ + 8).toNat = at_.toNat + 8 := by
      simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
    rw [zeros, ih _ (at_ + 8) below (by omega)]
    exact readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by omega) i hi k hk (by omega))

/-- Zeroing words of one block leaves the list of any blocks that lie clear of it as it was. -/
theorem ListFor.zeros {blocks : List Block} {head : UInt64} {size_class : Nat} {addresses : List UInt64}
    (block : UInt64) (bytes : Nat) (low : 1 ≤ block.toNat) (top : block.toNat + bytes ≤ 18446744073709551616)
    (clear : ∀ a, a ∈ addresses → 16 ≤ a.toNat ∧ a.toNat + 16 ≤ 18446744073709551616 ∧
      (a.toNat + 32 ≤ block.toNat ∨ block.toNat + bytes + 16 ≤ a.toNat)) (count : Nat) :
    ∀ (memory : UInt64 → Option UInt8) (at_ : UInt64), ListFor memory blocks head size_class addresses →
      at_.toNat + 8 * count ≤ bytes →
      ListFor (Mini.Alloc.zeros memory block at_ count) blocks head size_class addresses := by
  induction count with
  | zero => intro memory at_ h _; exact h
  | succ count ih =>
    intro memory at_ h fits
    have here : (block + at_).toNat = block.toNat + at_.toNat := by rw [UInt64.toNat_add]; omega
    have next : (at_ + 8).toNat = at_.toNat + 8 := by
      simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
    exact ih _ (at_ + 8)
      (h.frame (block + at_) 0 (by omega) (fun a ha => by
        obtain ⟨l, t, side⟩ := clear a ha
        exact ⟨l, by omega, by omega⟩))
      (by omega)

theorem states_differ : UInt64.ofNat inUse ≠ UInt64.ofNat freed := by decide

/-- Freeing a block that was handed out and is in use keeps the heap sound: the block joins the front of its
class's list, and every list is still a chain of freed blocks. -/
theorem free_sound (s : State) (base : Nat) (blocks : List Block) (b0 : Block) (m0 : b0 ∈ blocks)
    (lists : Array UInt64) (hlists : s.arrays "free_small" = some lists) (sound : Sound s base blocks)
    (live : readBytes s.memory (b0.address - 16 + 8) 8 = .ok (UInt64.ofNat inUse)) :
    Sound
      { s with
        arrays := put s.arrays "free_small" (some (lists.setIfInBounds b0.size_class.toNat b0.address))
        memory := writeBytes
          (zeros (writeBytes s.memory (b0.address - 16 + 8) (UInt64.ofNat freed) 8) b0.address 0
            (b0.size_class.toNat * 2))
          b0.address (lists.getD b0.size_class.toNat 0) 8 }
      base blocks := by
  obtain ⟨order, lists', hlists', hsize, each⟩ := sound
  have same : lists' = lists := Option.some.inj (hlists'.symm.trans hlists)
  subst same
  have laid := order.1
  have top : (s.globals "heap_at").toNat ≤ 18446744073709551616 := by
    have := (s.globals "heap_end").toNat_lt; have := order.2; omega
  have inside := laid.inside b0 m0
  have head0 := laid.header b0 m0
  simp only [Block.bytes] at inside
  have written : (b0.address - 16 + 8).toNat = b0.address.toNat - 8 := by
    simp only [UInt64.toNat_add, UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl,
      show (8 : UInt64).toNat = 8 from rfl]
    have := b0.address.toNat_lt; omega
  -- No block on any list is the one being freed: those are free, and this one is in use.
  have away : ∀ c addresses, ListFor s.memory blocks (lists'.getD c 0) c addresses →
      ∀ a, a ∈ addresses → a ≠ b0.address := by
    intro c addresses listed a ha e
    obtain ⟨_, _, _, _, state⟩ := listed.2.2 a ha
    rw [e, live] at state
    exact states_differ (Except.ok.inj state)
  -- So every listed block lies clear of it, and the three kinds of write leave every list as it was.
  have carried : ∀ c addresses, ListFor s.memory blocks (lists'.getD c 0) c addresses →
      ListFor
        (writeBytes
          (zeros (writeBytes s.memory (b0.address - 16 + 8) (UInt64.ofNat freed) 8) b0.address 0
            (b0.size_class.toNat * 2))
          b0.address (lists'.getD b0.size_class.toNat 0) 8)
        blocks (lists'.getD c 0) c addresses := by
    intro c addresses listed
    have place : ∀ a, a ∈ addresses → 16 ≤ a.toNat ∧ a.toNat + 16 ≤ 18446744073709551616 ∧
        (a.toNat + 32 ≤ b0.address.toNat ∨ b0.address.toNat + b0.size_class.toNat * 16 + 16 ≤ a.toNat) := by
      intro a ha
      obtain ⟨b, member, where_, _, _⟩ := listed.2.2 a ha
      have := laid.clear top b0 m0 b member (by rw [where_]; exact away c addresses listed a ha)
      simp only [Block.bytes] at this
      rw [where_] at this
      exact ⟨this.1, this.2.1, this.2.2.2.2⟩
    have marked := listed.frame (b0.address - 16 + 8) (UInt64.ofNat freed) (by rw [written]; omega)
      (fun a ha => by obtain ⟨l, t, side⟩ := place a ha; rw [written]; exact ⟨l, by omega, by omega⟩)
    have wiped := ListFor.zeros b0.address (b0.size_class.toNat * 16) (by omega) (by omega) place
      (b0.size_class.toNat * 2) _ 0 marked (by simp only [show (0 : UInt64).toNat = 0 from rfl]; omega)
    exact wiped.frame b0.address _ (by omega)
      (fun a ha => by obtain ⟨l, t, side⟩ := place a ha; exact ⟨l, by omega, by omega⟩)
  refine ⟨free_keeps s base blocks b0 m0 _ lists' order, lists'.setIfInBounds b0.size_class.toNat b0.address,
    by simp [put], by simpa using hsize, fun c hc => ?_⟩
  obtain ⟨addresses, listed⟩ := each c hc
  have moved := carried c addresses listed
  by_cases hsame : c = b0.size_class.toNat
  · subst hsame
    refine ⟨b0.address :: addresses, ?_⟩
    have at_head : (lists'.setIfInBounds b0.size_class.toNat b0.address).getD b0.size_class.toNat 0 = b0.address := by
      simp [Array.getD_eq_getD_getElem?, hsize, hc]
    rw [at_head]
    refine ⟨⟨rfl, ?_, lists'.getD b0.size_class.toNat 0, readBytes_writeBytes_word _ _ _, moved.1⟩,
      List.nodup_cons.mpr ⟨fun inList => away _ addresses listed _ inList rfl, moved.2.1⟩, fun a ha => ?_⟩
    · intro zero
      have := congrArg UInt64.toNat zero
      simp only [show (0 : UInt64).toNat = 0 from rfl] at this
      omega
    · rcases List.mem_cons.mp ha with rfl | later
      · refine ⟨b0, m0, rfl, rfl, ?_⟩
        rw [readBytes_writeBytes_other _ _ _ _ _ _
            (fun i hi k hk => below_apart _ _ (by rw [written]; omega) i hi k hk (by omega)),
          zeros_below _ _ _ _ _ (by rw [written]; omega)
            (by simp only [show (0 : UInt64).toNat = 0 from rfl]; omega)]
        exact readBytes_writeBytes_word _ _ _
      · exact moved.2.2 a later
  · refine ⟨addresses, ?_⟩
    have elsewhere : (lists'.setIfInBounds b0.size_class.toNat b0.address).getD c 0 = lists'.getD c 0 := by
      simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm hsame)]
    rw [elsewhere]; exact moved

/-! ## The program, on a sound heap

The three things the allocator does with a small block, each about the program itself: it does nothing C
leaves open, and it leaves a sound heap sound. One call's result meets the next call's conditions, so these
cover any sequence of small requests and frees, as long as there is room and what is freed is a block that
was handed out and is in use. -/

theorem getD_of_lt (lists : Array UInt64) (i : Nat) (h : i < lists.size) : lists.getD i 0 = lists[i] := by
  simp [Array.getD, h]

/-- A small request, when a freed block of its class is waiting. -/
theorem malloc_reuse_sound (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (base : Nat)
    (blocks : List Block) (lists : Array UInt64) (low : 1 ≤ size) (high : size ≤ 4096)
    (sound : Sound s base blocks) (hlists : s.arrays "free_small" = some lists)
    (waiting : lists.getD (smallClass size).toNat 0 ≠ 0) :
    ∃ b after, b ∈ blocks ∧ b.size_class = smallClass size ∧
      program.call outside (fuel + 20) "rt_malloc" [size] s = .ok (.gave (b.address - 16 + 16), after) ∧
      Sound after base blocks := by
  have fits := smallClass_fits size low high
  have csmall : (smallClass size).toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using fits.1
  have hsize : (smallClass size).toNat < lists.size := by
    obtain ⟨_, lists', hlists', size', _⟩ := sound
    rw [← Option.some.inj (hlists'.symm.trans hlists)]; omega
  obtain ⟨b0, link, m0, where0, class0, hlink, hstate, kept⟩ :=
    reuse_sound s base blocks lists (smallClass size).toNat csmall sound hlists waiting
  refine ⟨b0, _, m0, UInt64.toNat_inj.mp class0, ?_, kept⟩
  exact malloc_reuse outside fuel size s lists b0.address link low high hlists hsize
    (by rw [← getD_of_lt lists _ hsize, where0])
    (by rw [where0]; exact waiting) hlink hstate

/-- A small request, when no freed block of its class is waiting and the heap has room. -/
theorem malloc_fresh_sound (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (base : Nat)
    (blocks : List Block) (lists : Array UInt64) (low : 1 ≤ size) (high : size ≤ 4096)
    (sound : Sound s base blocks) (hlists : s.arrays "free_small" = some lists)
    (empty : lists.getD (smallClass size).toNat 0 = 0)
    (asked : s.globals "heap_asked" = 1) (started : s.globals "heap_at" ≠ 0)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16) :
    ∃ after, program.call outside (fuel + 20) "rt_malloc" [size] s = .ok (.gave (s.globals "heap_at" + 16), after) ∧
      Sound after base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) := by
  have fits := smallClass_fits size low high
  have csmall : (smallClass size).toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using fits.1
  have hsize : (smallClass size).toNat < lists.size := by
    obtain ⟨_, lists', hlists', size', _⟩ := sound
    rw [← Option.some.inj (hlists'.symm.trans hlists)]; omega
  exact ⟨afterFresh s size,
    malloc_fresh outside fuel size s lists low high hlists hsize (by rw [← getD_of_lt lists _ hsize]; exact empty)
      asked started room,
    fresh_sound s base blocks size low high sound room⟩

/-- Freeing a block that was handed out and is in use. -/
theorem free_small_sound (outside : Outside) (extra : Nat) (s : State) (base : Nat) (blocks : List Block)
    (lists : Array UInt64) (b : Block) (member : b ∈ blocks) (sound : Sound s base blocks)
    (hlists : s.arrays "free_small" = some lists)
    (live : readBytes s.memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat inUse)) :
    ∃ after, program.call outside (b.size_class.toNat * 2 + extra + 30) "rt_free" [b.address] s = .ok (.on, after) ∧
      Sound after base blocks := by
  have head := sound.1.1.header b member
  have small : b.size_class < 257 := by
    simp only [UInt64.lt_iff_toNat_lt, show (257 : UInt64).toNat = 257 from rfl]; exact head.2.2
  have hsize : b.size_class.toNat < lists.size := by
    obtain ⟨_, lists', hlists', size', _⟩ := sound
    rw [← Option.some.inj (hlists'.symm.trans hlists)]; omega
  refine ⟨_, free_small outside extra b.address b.size_class s lists live head.1 small hlists hsize, ?_⟩
  rw [← getD_of_lt lists _ hsize]
  exact free_sound s base blocks b member lists hlists sound live

/-- Where it starts: a heap from which nothing has been handed out, with every list empty, is sound. -/
theorem empty_sound (s : State) (within : (s.globals "heap_at").toNat ≤ (s.globals "heap_end").toNat)
    (hlists : s.arrays "free_small" = some (Array.replicate 257 0)) :
    Sound s (s.globals "heap_at").toNat [] :=
  ⟨⟨rfl, within⟩, Array.replicate 257 0, hlists, by simp, fun c hc =>
    ⟨[], by simp [ListFor, Chain, Array.getD, hc]⟩⟩

end Mini.Alloc
