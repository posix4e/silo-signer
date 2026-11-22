import Mini.Lang

/-! # Natural numbers: the small cases

Compiled Lean does most arithmetic on small numbers inline. Shifts, powers and logarithms it leaves to the
runtime. The small cases are answered here; an operand or a result that is not small goes to the big-number
code (`Mini/Number.lean`). A small number is a tagged word: the number shifted up one bit with the lowest
bit set. -/

namespace Mini.Small

def object : String := "lean_object *"
def box (e : Expr) : Expr := Expr.or (Expr.shl e 1) 1
def unbox (e : Expr) : Expr := Expr.shr e 1
def isWord (e : Expr) : Expr := Expr.ne (Expr.and e 1) 0
/-- The largest shift or exponent Lean's runtime takes, and the largest small number. -/
def most : Expr := .lit 0xFFFFFFFF
def largestSmall : Expr := .lit 0x7FFFFFFFFFFFFFFF
def tooBig (what : String) : Stmt := .outside none s!"lean_internal_panic(\"{what} exponent is too big\")"

def productFits : Function where
  name := "product_fits"
  about := "1 if the product of two words is a small number: it neither wraps nor reaches 2^63."
  parameters := ["a", "b"]
  body := [
    .branch (Expr.eq "a" 0) [.give 1] [],
    .set "product" ("a" * "b"),
    .branch (Expr.ne ("product" / "a") "b") [.give 0] [],
    .give (Expr.le "product" largestSmall)]

def toSize : Function where
  name := "rt_nat_to_size"
  about := "A natural number used as a size. Lean's runtime gives the value when it fits a word and reports \"out of\nmemory\" when it does not, since no array is that large. Lean's runtime also takes over the caller's\nreference to a number that is not small; this borrows, so a caller that owns such a number still has to\nrelease it."
  seen := some { result := "size_t", parameters := [object] }
  parameters := ["nat"]
  body := [
    .branch (isWord "nat") [.give (unbox "nat")] [],
    .callOther (some "size") "rt_big_nat_to_size" ["nat"],
    .give "size"]

def shiftLeft : Function where
  name := "lean_nat_shiftl"
  about := "`a <<< b`."
  seen := some { result := object, parameters := [object, object] }
  parameters := ["a1", "a2"]
  body := [
    .branch (Expr.eq "a1" (box 0)) [.give (box 0)] [],
    .branch (isWord "a2") [] [tooBig "Nat.shiftl"],
    .set "shift" (unbox "a2"),
    .branch (Expr.lt most "shift") [tooBig "Nat.shiftl"] [],
    .branch (isWord "a1")
      [.set "value" (unbox "a1"),
       -- Small if nothing is pushed into or past bit 63.
       .branch (Expr.lt "shift" 63)
         [.branch (Expr.eq (Expr.shr "value" (63 - "shift")) 0) [.give (box (Expr.shl "value" "shift"))] []] []] [],
    .callOther (some "result") "rt_big_nat_shiftl" ["a1", "shift"],
    .give "result"]

def power : Function where
  name := "lean_nat_pow"
  about := "`a ^ b`."
  seen := some { result := object, parameters := [object, object] }
  parameters := ["a1", "a2"]
  body := [
    .set "wide" 1,
    .branch (isWord "a2") [.branch (Expr.le (unbox "a2") most) [.set "wide" 0] []] [],
    .branch (Expr.ne "wide" 0)
      [.branch (Expr.eq "a1" (box 0)) [.give (box 0)] [],
       .branch (Expr.eq "a1" (box 1)) [.give (box 1)] [],
       tooBig "Nat.pow"] [],
    .set "exponent" (unbox "a2"),
    .branch (isWord "a1")
      [.set "base" (unbox "a1"),
       .set "left" "exponent",
       .set "result" 1,
       .set "fits" 1,
       -- Square and multiply, stopping as soon as anything leaves the small range.
       .loop (Expr.and (Expr.ne "left" 0) "fits") [
         .branch (Expr.ne (Expr.and "left" 1) 0)
           [.call (some "fits") "product_fits" ["result", "base"],
            .set "result" ("result" * "base")] [],
         .set "left" (Expr.shr "left" 1),
         .branch (Expr.and (Expr.ne "left" 0) "fits")
           [.call (some "fits") "product_fits" ["base", "base"],
            .set "base" ("base" * "base")] []],
       .branch (Expr.ne "fits" 0) [.give (box "result")] []] [],
    .callOther (some "result") "rt_big_nat_pow" ["a1", "exponent"],
    .give "result"]

def logarithm : Function where
  name := "lean_nat_log2"
  about := "The position of the highest set bit; 0 for 0 and 1."
  seen := some { result := object, parameters := [object] }
  parameters := ["a"]
  body := [
    .branch (isWord "a")
      [.set "value" (unbox "a"),
       .set "result" 0,
       .loop (Expr.le 2 "value") [.set "result" ("result" + 1), .set "value" ("value" / 2)],
       .give (box "result")] [],
    .callOther (some "result") "rt_big_nat_log2" ["a"],
    .give (box "result")]

def program : Program where
  about := "Natural numbers: shifts, powers and logarithms of the small ones."
  preamble := "#include \"big.h\"\n"
  globals := []
  arrays := []
  others := [
    ("rt_big_nat_to_size", { result := "size_t", parameters := [object] }),
    ("rt_big_nat_shiftl", { result := object, parameters := [object, "size_t"] }),
    ("rt_big_nat_pow", { result := object, parameters := [object, "size_t"] }),
    ("rt_big_nat_log2", { result := "size_t", parameters := [object] })]
  functions := [productFits, toSize, shiftLeft, power, logarithm]

end Mini.Small
