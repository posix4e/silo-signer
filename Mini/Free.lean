import Mini.Lang

/-! # Giving up references, and freeing

Its C is printed when the runtime is built (`scripts/print-runtime`). An object is addressed by a word; a word with its lowest bit set is
not an object but a small value, and is never looked into.

An object's first word, as Lean lays it out (`lean_object` in `<lean/lean.h>`, on a little-endian machine):
the reference count in the low 32 bits, a size field in the next 16, a count of fields or other small number
in the next 8, and the kind of object in the top 8. -/

namespace Mini.Free

/-- The largest kind that is a constructor; the kinds above it are these. -/
def maxConstructor : Expr := 243
def closure : Expr := 245
def array : Expr := 246
def scalarArray : Expr := 248
def string : Expr := 249
def bigNumber : Expr := 250
def thunk : Expr := 251
def reference : Expr := 253
def external : Expr := 254

/-- The 48 bits of a header that hold the count and the size field, and the 16 that do not. -/
def linkBits : Expr := .lit 0x0000FFFFFFFFFFFF
def keptBits : Expr := .lit 0xFFFF000000000000
def countBits : Expr := .lit 0xFFFFFFFF

def release : Function where
  name := "release"
  about := "Gives up one reference to `o`. If it was the last, `o` joins the objects waiting to be freed: they\nare linked through their own headers, in the 48 bits that held the count and the size field, which leaves\nthe kind and the field count in place to say how to walk the object when its turn comes. A count of 0 is\na permanent object, and one with its top bit set has overflowed and frozen: neither is ever freed."
  parameters := ["o", "waiting"]
  body := [
    .branch (Expr.ne (Expr.and "o" 1) 0) [.give "waiting"] [],
    .set "header" (.load "o"),
    .set "count" (Expr.and "header" countBits),
    .branch (Expr.and (Expr.lt 1 "count") (Expr.lt "count" (.lit 0x80000000)))
      [.store "o" ("header" - 1), .give "waiting"] [],
    .branch (Expr.eq "count" 1)
      [.store "o" (Expr.or (Expr.and "header" keptBits) "waiting"), .give "o"] [],
    .give "waiting"]

def releaseAll : Function where
  name := "release_all"
  about := "Gives up one reference to each of the `count` objects whose addresses start at `at`."
  parameters := ["at", "count", "waiting"]
  body := [
    .set "i" 0,
    .loop (Expr.lt "i" "count") [
      .call (some "waiting") "release" [.load ("at" + "i" * 8), "waiting"],
      .set "i" ("i" + 1)],
    .give "waiting"]

def freeBlock : Stmt := .outside none "rt_free((void *)o)"

def freeOne : Function where
  name := "free_one"
  about := "Frees `o`, whose last reference is gone, and returns the waiting list with whatever that released."
  parameters := ["o", "waiting"]
  body := [
    .set "header" (.load "o"),
    .set "kind" (Expr.shr "header" 56),
    .branch (Expr.le "kind" maxConstructor)
      [.call (some "waiting") "release_all" ["o" + 8, Expr.and (Expr.shr "header" 48) 0xFF, "waiting"],
       freeBlock,
       .give "waiting"] [],
    .branch (Expr.eq "kind" closure)
      -- The function, then how many arguments it takes and how many it has, 16 bits each, then those it has.
      [.call (some "waiting") "release_all" ["o" + 24, Expr.and (Expr.shr (.load ("o" + 16)) 16) 0xFFFF, "waiting"]]
    [.branch (Expr.eq "kind" array)
      -- Its size, its capacity, then its elements.
      [.call (some "waiting") "release_all" ["o" + 24, .load ("o" + 8), "waiting"]]
    [.branch (Expr.or (Expr.or (Expr.eq "kind" scalarArray) (Expr.eq "kind" string)) (Expr.eq "kind" bigNumber))
      []
    [.branch (Expr.eq "kind" thunk)
      -- Its value, then the closure that computes it; either may be absent.
      [.set "value" (.load ("o" + 8)),
       .set "computes" (.load ("o" + 16)),
       .branch (Expr.ne "computes" 0) [.call (some "waiting") "release" ["computes", "waiting"]] [],
       .branch (Expr.ne "value" 0) [.call (some "waiting") "release" ["value", "waiting"]] []]
    [.branch (Expr.eq "kind" reference)
      [.set "value" (.load ("o" + 8)),
       .branch (Expr.ne "value" 0) [.call (some "waiting") "release" ["value", "waiting"]] []]
    [.branch (Expr.eq "kind" external)
      -- Its class, whose first word is the function that finishes with its data, then the data.
      [.outside none "((void (*)(void *))mini_load(mini_load(o + 8)))((void *)mini_load(o + 16))"]
      [.stop "an object of a kind this runtime does not have (a task or promise) was freed"]]]]]],
    freeBlock,
    .give "waiting"]

def decRefCold : Function where
  name := "lean_dec_ref_cold"
  about := "Called by compiled Lean when it gives up a reference and the count is not above one. Freeing an object\nfrees what it alone was keeping alive, which can be a very long chain, so nothing here calls itself: one\nobject is freed at a time, and what that releases waits its turn."
  seen := some { result := "void", parameters := ["lean_object *"] }
  parameters := ["o"]
  body := [
    .branch (Expr.ne (Expr.and (.load "o") countBits) 1) [.give 0] [],
    .set "waiting" 0,
    .loop 1 [
      .call (some "waiting") "free_one" ["o", "waiting"],
      .branch (Expr.eq "waiting" 0) [.give 0] [],
      .set "o" "waiting",
      .set "waiting" (Expr.and (.load "o") linkBits)],
    .give 0]

def program : Program where
  about := "Giving up references, and freeing what the last one was keeping alive."
  preamble := "#include \"rt.h\"\n"
  globals := []
  arrays := []
  functions := [release, releaseAll, freeOne, decRefCold]

end Mini.Free
