import Mini.Lang

/-! # Whether a function's time can depend on a secret

A check of a function's text, not a proof about the machine: it follows what may hold a secret (the
parameters said to, anything read from memory, and anything computed from those) and refuses the function if
a secret decides

- a branch or a loop condition, which decides what runs;
- an address read or written, or an index, which decides what the cache holds;
- an operand of a division, which takes longer on some values on most processors;

or if it calls anything, whose time this cannot see. Shifts, sums, products and logic take the same time
whatever their values on the processors this runs on (and Intel's data-independent timing mode, which the
boot stub turns on where offered, is the promise of that).

This is the discipline of "constant-time" code as BearSSL and libsodium write it, and what tools such as
ctgrind and dudect check of compiled code by watching it run. Here it is checked of the text the C is printed
from, before anything runs. -/

namespace Mini

/-- Whether the value may depend on a secret, given the locals that may. -/
def Expr.secret (t : List String) : Expr → Bool
  | .lit _ => false
  | .var name => t.contains name
  | .global _ => false
  | .item _ i => i.secret t
  | .load _ => true
  | .part _ _ => true
  | .op _ a b => a.secret t || b.secret t

/-- The first way the expression lets a secret decide its time, if any. -/
def Expr.leak (t : List String) : Expr → Option String
  | .item array i => if i.secret t then some s!"an index into {array} depends on a secret" else i.leak t
  | .load address | .part _ address =>
    if address.secret t then some "an address read depends on a secret" else address.leak t
  | .op .div a b =>
    if a.secret t || b.secret t then some "a division depends on a secret" else (a.leak t).orElse fun _ => b.leak t
  | .op _ a b => (a.leak t).orElse fun _ => b.leak t
  | _ => none

namespace Constant

def mark (t : List String) (name : String) (secret : Bool) : List String :=
  if secret && !t.contains name then name :: t else t

mutual
  /-- The locals that may hold a secret after the statements, or the first leak. `fuel` bounds how often a
  loop's body is gone over before what it can carry around has stopped growing; it only grows, and there are
  only so many locals. -/
  def statements (fuel : Nat) (t : List String) : List Stmt → Except String (List String)
    | [] => pure t
    | s :: rest => do statements fuel (← statement fuel t s) rest
  def statement (fuel : Nat) (t : List String) : Stmt → Except String (List String)
    | .set name value => do
      if let some why := value.leak t then throw why
      pure (mark t name (value.secret t))
    | .setGlobal _ value | .setItem _ _ value => do
      if let some why := value.leak t then throw why
      if value.secret t then throw "a secret is kept where a later caller could time its use" else pure t
    | .store address value | .storePart _ address value => do
      if let some why := address.leak t then throw why
      if let some why := value.leak t then throw why
      if address.secret t then throw "an address written depends on a secret" else pure t
    | .branch condition yes no => do
      if let some why := condition.leak t then throw why
      if condition.secret t then throw "a branch depends on a secret"
      let t ← statements fuel t yes
      statements fuel t no
    | .loop condition body =>
      match fuel with
      | 0 => throw "the check ran out of steps"
      | fuel + 1 => do
        if let some why := condition.leak t then throw why
        if condition.secret t then throw "a loop condition depends on a secret"
        let after ← statements fuel t body
        if after.length == t.length then pure t else statement fuel after (.loop condition body)
    | .call _ function _ => throw s!"a call of {function}, whose time this does not see"
    | .callOther _ function _ => throw s!"a call of {function}, whose time this does not see"
    | .outside _ c => throw s!"a call of {c}, whose time this does not see"
    | .hide _ | .stop _ => pure t
    | .keep address => do
      if let some why := address.leak t then throw why
      pure t
    | .give value => do
      if let some why := value.leak t then throw why
      pure t
end

/-- Whether `f` lets a secret decide its time, with `secrets` the parameters that hold one. -/
def check (f : Function) (secrets : List String) : Except String Unit := do
  let _ ← statements 64 secrets f.body

end Constant

end Mini
