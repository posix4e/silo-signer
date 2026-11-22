import Mini.Lang

/-! # What a program means

Running a program, a step at a time, in Lean. This is the language's definition: the printed C is meant to
do what this does, wherever this does not fail.

It fails where C would leave the outcome open, so that a program shown never to fail here does not depend on
any of it: dividing by zero, shifting by 64 or more, reading or writing outside a global array, reading a
local that was never set, and reading memory nothing has written. Arithmetic wraps, as it does on the
machine. Memory is bytes; a word is eight of them, lowest first.

A call out of the program is whatever `outside` says it is. Running out of `fuel` is a failure too: a
function that needs more steps than it was given has not been shown to finish. -/

namespace Mini

/-- Everything a program can see and change. Each part is a function, changed by putting a new answer in front
of the old one: slow to run for long, and simple to reason about. -/
structure State where
  globals : String → UInt64 := fun _ => 0
  arrays : String → Option (Array UInt64) := fun _ => none
  /-- The byte at an address, where something has been written. -/
  memory : UInt64 → Option UInt8 := fun _ => none

/-- `f`, with a new answer for one question. -/
def put {α β : Type} [DecidableEq α] (f : α → β) (key : α) (value : β) : α → β :=
  fun k => if k = key then value else f k

/-- How a function or a run of statements ends. -/
inductive Ending
  | on
  | gave (value : UInt64)
  | stopped (why : String)

abbrev Locals := String → Option UInt64

/-- What a call out of the program does: given the function's name (or the C text) and its arguments, a
result and the state after. -/
abbrev Outside := String → List UInt64 → State → Except String (UInt64 × State)

/-- The `count` bytes at an address as a number, lowest first. -/
def readBytes (memory : UInt64 → Option UInt8) (address : UInt64) : Nat → Except String UInt64
  | 0 => pure 0
  | count + 1 =>
    match memory address with
    | none => throw s!"a read at {address}, which nothing has written"
    | some byte => do pure (byte.toUInt64 ||| ((← readBytes memory (address + 1) count) <<< 8))

/-- Memory with the lowest `count` bytes of a word written at an address, lowest first. -/
def writeBytes (memory : UInt64 → Option UInt8) (address word : UInt64) : Nat → UInt64 → Option UInt8
  | 0 => memory
  | count + 1 => writeBytes (put memory address (some word.toUInt8)) (address + 1) (word >>> 8) count

def Op.run (o : Op) (a b : UInt64) : Except String UInt64 :=
  let truth (p : Bool) : UInt64 := if p then 1 else 0
  match o with
  | .add => pure (a + b) | .sub => pure (a - b) | .mul => pure (a * b)
  | .div => if b == 0 then throw "division by zero" else pure (a / b)
  | .shl => if b ≥ 64 then throw "a shift by 64 or more" else pure (a <<< b)
  | .shr => if b ≥ 64 then throw "a shift by 64 or more" else pure (a >>> b)
  | .and => pure (a &&& b) | .or => pure (a ||| b) | .xor => pure (a ^^^ b)
  | .eq => pure (truth (a == b)) | .ne => pure (truth (a != b))
  | .lt => pure (truth (a < b)) | .le => pure (truth (a ≤ b))

def Expr.run (s : State) (locals : Locals) : Expr → Except String UInt64
  | .lit value => pure value
  | .var name => match locals name with
    | some value => pure value
    | none => throw s!"the local {name} is read before it is set"
  | .global name => pure (s.globals name)
  | .item array i => do
    let i ← i.run s locals
    match s.arrays array with
    | none => throw s!"no array {array}"
    | some items => if h : i.toNat < items.size then pure items[i.toNat] else throw s!"{array}[{i}] is outside it"
  | .load address => do readBytes s.memory (← address.run s locals) 8
  | .part bytes address => do
    if bytes != 1 && bytes != 2 && bytes != 4 then throw s!"a read of {bytes} bytes"
    readBytes s.memory (← address.run s locals) bytes
  | .op o a b => do o.run (← a.run s locals) (← b.run s locals)

def bind (locals : Locals) : List String → List UInt64 → Locals
  | name :: names, value :: values => bind (put locals name (some value)) names values
  | _, _ => locals

mutual
  def Stmt.run (p : Program) (outside : Outside) : Nat → Stmt → State → Locals → Except String (Ending × State × Locals)
    | 0, _, _, _ => throw "out of fuel"
    | fuel + 1, statement, s, locals =>
      match statement with
      | .set name value => do pure (.on, s, put locals name (some (← value.run s locals)))
      | .setGlobal name value => do
        pure (.on, { s with globals := put s.globals name (← value.run s locals) }, locals)
      | .setItem array i value => do
        let i ← i.run s locals
        let value ← value.run s locals
        match s.arrays array with
        | none => throw s!"no array {array}"
        | some items =>
          if i.toNat < items.size then
            pure (.on, { s with arrays := put s.arrays array (some (items.setIfInBounds i.toNat value)) }, locals)
          else throw s!"{array}[{i}] is outside it"
      | .store address value => do
        let address ← address.run s locals
        pure (.on, { s with memory := writeBytes s.memory address (← value.run s locals) 8 }, locals)
      | .storePart bytes address value => do
        if bytes != 1 && bytes != 2 && bytes != 4 then throw s!"a write of {bytes} bytes"
        let address ← address.run s locals
        pure (.on, { s with memory := writeBytes s.memory address (← value.run s locals) bytes }, locals)
      | .branch condition yes no => do
        if (← condition.run s locals) != 0 then runAll p outside fuel yes s locals
        else runAll p outside fuel no s locals
      | .loop condition body => do
        if (← condition.run s locals) == 0 then pure (.on, s, locals) else
        match ← runAll p outside fuel body s locals with
        | (.on, s, locals) => Stmt.run p outside fuel (.loop condition body) s locals
        | ended => pure ended
      | .call result function arguments => do
        let values ← arguments.mapM (·.run s locals)
        match p.functions.find? (·.name == function) with
        | none => throw s!"no function {function}"
        | some f =>
          match ← runAll p outside fuel f.body s (bind (fun _ => none) f.parameters values) with
          | (.stopped why, s, _) => pure (.stopped why, s, locals)
          | (.gave value, s, _) => pure (.on, s, match result with | some name => put locals name (some value) | none => locals)
          | (.on, s, _) => pure (.on, s, match result with | some name => put locals name (some 0) | none => locals)
      | .callOther result function arguments => do
        let values ← arguments.mapM (·.run s locals)
        let (value, s) ← outside function values s
        pure (.on, s, match result with | some name => put locals name (some value) | none => locals)
      | .outside result c => do
        let (value, s) ← outside c [] s
        pure (.on, s, match result with | some name => put locals name (some value) | none => locals)
      | .hide name => do
        let _ ← (Expr.var name).run s locals
        pure (.on, s, locals)
      | .keep address => do
        let _ ← address.run s locals
        pure (.on, s, locals)
      | .stop why => pure (.stopped why, s, locals)
      | .give value => do pure (.gave (← value.run s locals), s, locals)
  def runAll (p : Program) (outside : Outside) : Nat → List Stmt → State → Locals → Except String (Ending × State × Locals)
    | 0, _, _, _ => throw "out of fuel"
    | _, [], s, locals => pure (.on, s, locals)
    | fuel + 1, statement :: rest, s, locals => do
      match ← Stmt.run p outside fuel statement s locals with
      | (.on, s, locals) => runAll p outside fuel rest s locals
      | ended => pure ended
end

/-- A program's state before anything has run: every global zero, every array full of zeros. -/
def Program.start (p : Program) : State :=
  { arrays := p.arrays.foldl (fun arrays (name, size) => put arrays name (some (Array.replicate size 0))) (fun _ => none) }

/-- Calls a function by name. -/
def Program.call (p : Program) (outside : Outside) (fuel : Nat) (function : String) (arguments : List UInt64)
    (s : State) : Except String (Ending × State) :=
  match p.functions.find? (·.name == function) with
  | none => throw s!"no function {function}"
  | some f => do
    let (ending, s, _) ← runAll p outside fuel f.body s (bind (fun _ => none) f.parameters arguments)
    pure (ending, s)

end Mini
