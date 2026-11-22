import Mini.Lang

/-! # Sums and products of sizes that stop instead of wrapping

What Lean's header does with `__builtin_add_overflow` and `__builtin_mul_overflow` (`lean_usize_add_checked`,
`lean_usize_mul_checked`), written in the language, so that a program sizing an object says what it does
instead of assuming what something outside it does. A program that uses them lists `Checked.functions` among
its own; the C printed from each is a few lines.

A sum wrapped if it came out smaller than what was added to. A product wrapped if dividing it by one factor
does not give back the other: the test GCC and Clang fall back to on machines without a flag for it. -/

namespace Mini.Checked

def overflow : String := "a size was too large to represent"

def add : Function where
  name := "add_checked"
  parameters := ["a", "b"]
  body := [
    .set "r" ("a" + "b"),
    .branch (Expr.lt "r" "a") [.stop overflow] [],
    .give "r"]

def mul : Function where
  name := "mul_checked"
  parameters := ["a", "b"]
  body := [
    .set "r" ("a" * "b"),
    .branch (Expr.ne "a" 0) [.branch (Expr.ne ("r" / "a") "b") [.stop overflow] []] [],
    .give "r"]

def functions : List Function := [add, mul]

end Mini.Checked
