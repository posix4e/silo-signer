import Mini.Lang

/-! # Hashing bytes

Lean hashes strings and byte arrays with the 64-bit MurmurHash2 (MurmurHash64A, by Austin Appleby, public
domain), and compiled Lean depends on the exact values: a `HashMap` built at compile time and one probed at
run time have to agree. So this is that function, bit for bit. -/

namespace Mini.Hash

def m : Expr := .lit 0xc6a4a7935bd1e995

def hashBytes : Function where
  name := "rt_hash_bytes"
  seen := some { result := "uint64_t", parameters := ["uint8_t const *", "size_t", "uint64_t"] }
  parameters := ["bytes", "length", "seed"]
  body := [
    .set "h" (Expr.xor "seed" ("length" * m)),
    .set "end" ("bytes" + ("length" / 8) * 8),
    .set "at" "bytes",
    -- Eight bytes at a time, lowest first.
    .loop (Expr.ne "at" "end") [
      .set "k" (.load "at" * m),
      .set "k" (Expr.xor "k" (Expr.shr "k" 47) * m),
      .set "h" (Expr.xor "h" "k" * m),
      .set "at" ("at" + 8)],
    -- Then the one to seven that are left.
    .set "left" (Expr.and "length" 7),
    .set "i" 0,
    .loop (Expr.lt "i" "left") [
      .set "h" (Expr.xor "h" (Expr.shl (.part 1 ("at" + "i")) ("i" * 8))),
      .set "i" ("i" + 1)],
    .branch (Expr.ne "left" 0) [.set "h" ("h" * m)] [],
    .set "h" (Expr.xor "h" (Expr.shr "h" 47) * m),
    .give (Expr.xor "h" (Expr.shr "h" 47))]

def program : Program where
  about := "Hashing bytes: MurmurHash64A, as Lean's runtime computes it."
  preamble := "#include \"rt.h\"\n"
  globals := []
  arrays := []
  functions := [hashBytes]

end Mini.Hash
