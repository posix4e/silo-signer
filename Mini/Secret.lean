import Mini.Lang

/-! # Comparing and choosing in time that does not depend on secrets

Two functions for code that handles a secret: whether two byte arrays of the same, public length are equal,
and choosing between two words by a secret bit. Neither has a branch, a loop condition, an address or a
division that depends on a secret, which `Mini/Constant.lean` checks, so the work they do and the memory they
touch are the same whatever the secret is. `memcmp` stops at the first difference, which tells anyone timing
it how much of a guess was right; these do not stop.

They are the patterns of libsodium (`sodium_memcmp`, `crypto_verify_32`) and BearSSL (`MUX` and `EQ` in
`inner.h`): differences are gathered with OR rather than acted on, and a choice is made with a mask rather
than a branch. As there, what is accumulated is hidden from the compiler, which could otherwise see that
once it is non-zero it stays non-zero and stop the loop early.

Called from Lean through `Secret.lean`. -/

namespace Mini.Secret

def object : String := "lean_object *"

def equal : Function where
  name := "silo_secret_equal"
  about := "Whether the first `size` bytes of two byte arrays are equal, reading every one of them. `size` is public,\nand no larger than either array (Secret.lean sees to that)."
  seen := some { result := "uint8_t", parameters := [object, object, "size_t"] }
  parameters := ["a", "b", "size"]
  body := [
    .set "differ" 0,
    .set "i" 0,
    .loop (Expr.lt "i" "size") [
      .set "differ" (Expr.or "differ" (Expr.xor (.part 1 ("a" + 24 + "i")) (.part 1 ("b" + 24 + "i")))),
      .hide "differ",
      .set "i" ("i" + 1)],
    -- `differ` is at most 255: one less than it has its top bit set exactly when it is zero.
    .give (Expr.shr ("differ" - 1) 63)]

def select : Function where
  name := "silo_secret_select"
  about := "`x` if `bit` is 1, `y` if it is 0."
  seen := some { result := "uint64_t", parameters := ["uint8_t", "uint64_t", "uint64_t"] }
  parameters := ["bit", "x", "y"]
  body := [
    .set "mask" (0 - Expr.and "bit" 1),
    .hide "mask",
    .give (Expr.xor "y" (Expr.and (Expr.xor "x" "y") "mask"))]

/-- Which of each function's parameters are secret. What it reads from memory always is. -/
def secrets : List (String × List String) := [("silo_secret_equal", []), ("silo_secret_select", ["bit", "x", "y"])]

def program : Program where
  about := "Comparing and choosing in time that does not depend on secrets."
  preamble := "#include <lean/lean.h>\n"
  globals := []
  arrays := []
  functions := [equal, select]

end Mini.Secret
