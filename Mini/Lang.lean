/-! # A small language for the code under Lean

The allocator, reference counts and object layout are what compiled Lean stands on, so they cannot be written
in Lean as it is compiled. They can be written as *data* in Lean: programs in a language small enough to say
exactly what each step does, from which the C is printed (`Mini/Print.lean`). What is reasoned about and what
is compiled are then the same text.

The language has one type, the 64-bit word. A program has global words, global arrays of words, and
functions from words to a word. Memory is read and written a word at a time at an address that is itself a
word. There is no pointer type to get wrong and nothing is implicit: no conversions, no overflow that is not
wrap-around, no evaluation order to choose (calls are statements, so an expression has no effects). -/

namespace Mini

inductive Op
  | add | sub | mul | div | shl | shr | and | or | xor
  /-- Comparisons of words as unsigned numbers: 1 if it holds, 0 if not. -/
  | eq | ne | lt | le
  deriving Repr, DecidableEq

inductive Expr
  | lit (value : UInt64)
  /-- A parameter or a local. -/
  | var (name : String)
  | global (name : String)
  /-- Element `i` of a global array. The printed C checks nothing: staying inside is the program's to show. -/
  | item (array : String) (i : Expr)
  /-- The word in memory at an address. -/
  | load (address : Expr)
  /-- The 1, 2 or 4 bytes in memory at an address, as a word with zeros above them. -/
  | part (bytes : Nat) (address : Expr)
  | op (o : Op) (a b : Expr)
  deriving Repr

inductive Stmt
  | set (name : String) (value : Expr)
  | setGlobal (name : String) (value : Expr)
  | setItem (array : String) (i value : Expr)
  | store (address value : Expr)
  /-- Writes the lowest 1, 2 or 4 bytes of a word to memory. -/
  | storePart (bytes : Nat) (address value : Expr)
  | branch (condition : Expr) (yes no : List Stmt)
  | loop (condition : Expr) (body : List Stmt)
  /-- A call of one of the program's own functions. -/
  | call (result : Option String) (function : String) (arguments : List Expr)
  /-- A call of a function that is not the program's: one the program names among its `others`, with the C
  types it takes and gives. What it does is an assumption wherever it is used. -/
  | callOther (result : Option String) (function : String) (arguments : List Expr)
  /-- A call out of the program for which that is not enough, as the C to write. -/
  | outside (result : Option String) (c : String)
  /-- Nothing, as far as the language is concerned; the compiler is told it no longer knows what the local
  holds. Without it a compiler may see that a mask computed with no branch is only ever all ones or zero,
  and put the branch back (Linux's `OPTIMIZER_HIDE_VAR`). -/
  | hide (name : String)
  /-- Nothing, as far as the language is concerned; the compiler is told the memory at the address may be
  read after this, so the writes before it have to happen. That is what keeps a wipe from being dropped as a
  store nothing reads (`explicit_bzero` in OpenBSD, `memset_s` in C11). -/
  | keep (address : Expr)
  /-- Stop the machine, saying why. Nothing after it runs. -/
  | stop (why : String)
  | give (value : Expr)
  deriving Repr

/-- How a function is seen from C, if it is: the C types of its result and of its parameters. -/
structure Seen where
  result : String
  parameters : List String
  deriving Repr

structure Function where
  name : String
  parameters : List String
  body : List Stmt
  seen : Option Seen := none
  about : String := ""
  deriving Repr

structure Program where
  about : String
  /-- What the printed file has to declare first: includes, and the functions called from `outside`. -/
  preamble : String
  globals : List String
  arrays : List (String × Nat)
  /-- The functions outside the program that it calls, each with how C sees it. -/
  others : List (String × Seen) := []
  functions : List Function
  deriving Repr

/-! Writing programs down. -/

instance : OfNat Expr n := ⟨.lit (UInt64.ofNat n)⟩
instance : Add Expr := ⟨.op .add⟩
instance : Sub Expr := ⟨.op .sub⟩
instance : Mul Expr := ⟨.op .mul⟩
instance : Div Expr := ⟨.op .div⟩
instance : Coe String Expr := ⟨.var⟩

/-! What the shorthand stands for, for proofs to see through it. -/
@[simp] theorem Expr.ofNat_eq (n : Nat) : (OfNat.ofNat n : Expr) = .lit (UInt64.ofNat n) := rfl
@[simp] theorem Expr.add_eq (a b : Expr) : a + b = .op .add a b := rfl
@[simp] theorem Expr.sub_eq (a b : Expr) : a - b = .op .sub a b := rfl
@[simp] theorem Expr.mul_eq (a b : Expr) : a * b = .op .mul a b := rfl
@[simp] theorem Expr.div_eq (a b : Expr) : a / b = .op .div a b := rfl

def Expr.shl (a b : Expr) : Expr := .op .shl a b
def Expr.shr (a b : Expr) : Expr := .op .shr a b
def Expr.and (a b : Expr) : Expr := .op .and a b
def Expr.or (a b : Expr) : Expr := .op .or a b
def Expr.xor (a b : Expr) : Expr := .op .xor a b
def Expr.eq (a b : Expr) : Expr := .op .eq a b
def Expr.ne (a b : Expr) : Expr := .op .ne a b
def Expr.lt (a b : Expr) : Expr := .op .lt a b
def Expr.le (a b : Expr) : Expr := .op .le a b

/-- `index` made zero, without a branch, unless it is below `size`: the bounds check before it may be guessed
wrong by a processor running ahead, and this is what it then reads with. Both must be below 2^63; in that
range the mask is all ones exactly when `index < size`. Linux's `array_index_nospec` (include/linux/nospec.h),
whose x86 version is two instructions of assembly; this is its portable form, with the mask hidden from the
compiler so it cannot be turned back into a branch. -/
def Stmt.inBounds (index : String) (size : Expr) : List Stmt := [
  .set "nospec_mask" (Expr.op .sub (Expr.shr (Expr.or (.var index) (size - 1 - .var index)) 63) 1),
  .hide "nospec_mask",
  .set index (Expr.and (.var index) (.var "nospec_mask"))]

end Mini
