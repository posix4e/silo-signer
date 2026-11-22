import Mini.Lang
import Mini.Checked

/-! # Arrays and byte arrays

Both are Lean's header, a size, a capacity, and then the elements: for an array, one word each, an object or
a tagged value; for a byte array, the bytes themselves (the header's small field says how wide an element
is, for the kinds that are wider).

Both grow in place when the caller holds the only reference and there is room, and are copied otherwise. One
marked linear (`markLinear`, which is how a secret is kept from being duplicated; the mark is the top bit of
the header's small field) stops the machine if it would have to be copied because someone else still holds
it. Lean's own runtime only does that when asked through an environment variable. -/

namespace Mini.Array

def object : String := "lean_object *"
def arrayHeader : Expr := .lit (UInt64.ofNat (1 + 246 * 2 ^ 56))
def bytesKind : Expr := .lit (UInt64.ofNat (248 * 2 ^ 56))
def linearMark : Expr := .lit (UInt64.ofNat (2 ^ 55))

def sizeOf (a : Expr) : Expr := .load (a + 8)
def capacityOf (a : Expr) : Expr := .load (a + 16)
def exclusive (a : Expr) : Expr := Expr.eq (Expr.and (.load a) (.lit 0xFFFFFFFF)) 1
def linear (a : Expr) : Expr := Expr.ne (Expr.and (.load a) linearMark) 0
/-- How wide an element of a byte array or its like is. -/
def widthOf (a : Expr) : Expr := Expr.and (Expr.shr (.load a) 48) 0x7F
def slot (a i : Expr) : Expr := a + 24 + i * 8
def keepMark (from_ to : String) : Stmt :=
  .branch (linear from_) [.store to (Expr.or (.load to) linearMark)] []
def drop (o : Expr) : Stmt := .callOther none "lean_dec" [o]
def copyBytes (to from_ count : Expr) : Stmt := .callOther none "memcpy" [to, from_, count]

def refuse : Function where
  name := "refuse_copy_of_linear"
  parameters := ["o"]
  body := [.branch (linear "o") [.stop "a value marked linear was used where it would have to be copied"] []]

def arrayNew : Function where
  name := "array_new"
  parameters := ["size", "capacity"]
  body := [
    .callOther (some "r") "lean_alloc_object" [24 + "capacity" * 8],
    .store "r" arrayHeader,
    .store ("r" + 8) "size",
    .store ("r" + 16) "capacity",
    .give "r"]

def bytesNew : Function where
  name := "bytes_new"
  parameters := ["width", "size", "capacity"]
  body := [
    .call (some "room") "mul_checked" ["width", "capacity"],
    .call (some "room") "add_checked" [24, "room"],
    .callOther (some "r") "lean_alloc_object" ["room"],
    .store "r" (Expr.or (Expr.or 1 (Expr.shl "width" 48)) bytesKind),
    .store ("r" + 8) "size",
    .store ("r" + 16) "capacity",
    .give "r"]

def copyExpand : Function where
  name := "lean_copy_expand_array"
  about := "A copy of `a` with the same elements, and room to grow if `expand`. Gives up `a`."
  seen := some { result := object, parameters := [object, "bool"] }
  parameters := ["a", "expand"]
  body := [
    .set "size" (sizeOf "a"),
    .set "capacity" (capacityOf "a"),
    .branch (Expr.ne "expand" 0)
      [.call (some "capacity") "add_checked" ["capacity", 1],
       .call (some "capacity") "mul_checked" ["capacity", 2]] [],
    .call (some "r") "array_new" ["size", "capacity"],
    keepMark "a" "r",
    .branch (exclusive "a")
      [copyBytes ("r" + 24) ("a" + 24) ("size" * 8),
       .callOther none "lean_free_object" ["a"]]
      [.set "i" 0,
       .loop (Expr.lt "i" "size") [
         .set "element" (.load (slot "a" "i")),
         .store (slot "r" "i") "element",
         .callOther none "lean_inc" ["element"],
         .set "i" ("i" + 1)],
       drop "a"],
    .give "r"]

def copyExpandNonlinear : Function where
  name := "lean_copy_expand_array_nonlinear"
  seen := some { result := object, parameters := [object, "bool"] }
  parameters := ["a", "expand"]
  body := [
    .call none "refuse_copy_of_linear" ["a"],
    .call (some "r") "lean_copy_expand_array" ["a", "expand"],
    .give "r"]

def push : Function where
  name := "lean_array_push"
  seen := some { result := object, parameters := [object, object] }
  parameters := ["a", "v"]
  body := [
    .set "size" (sizeOf "a"),
    .set "capacity" (capacityOf "a"),
    .set "r" "a",
    .branch (exclusive "a")
      [.branch (Expr.lt "size" "capacity") [] [.call (some "r") "lean_copy_expand_array" ["a", 1]]]
      [.call (some "r") "lean_copy_expand_array_nonlinear" ["a", Expr.lt "capacity" (2 * "size" + 1)]],
    .set "size" (sizeOf "r"),
    .store (slot "r" "size") "v",
    .store ("r" + 8) ("size" + 1),
    .give "r"]

def copyBytesArray : Function where
  name := "copy_sarray"
  about := "A copy of `a` with room for `capacity` elements. Gives up `a`."
  parameters := ["a", "capacity"]
  body := [
    .set "width" (widthOf "a"),
    .set "size" (sizeOf "a"),
    .call (some "r") "bytes_new" ["width", "size", "capacity"],
    keepMark "a" "r",
    copyBytes ("r" + 24) ("a" + 24) ("width" * "size"),
    drop "a",
    .give "r"]

def withCapacity : Function where
  name := "sarray_with_capacity"
  about := "`a` with room for at least `least` elements; twice that when it has to grow and `exact` is false."
  parameters := ["a", "least", "exact"]
  body := [
    .branch (Expr.le "least" (capacityOf "a")) [.give "a"] [],
    .set "capacity" "least",
    .branch (Expr.eq "exact" 0) [.call (some "capacity") "mul_checked" ["least", 2]] [],
    .branch (exclusive "a") [] [.call none "refuse_copy_of_linear" ["a"]],
    .call (some "r") "copy_sarray" ["a", "capacity"],
    .give "r"]

def madeExclusive : Function where
  name := "sarray_exclusive"
  about := "`a` if the caller holds the only reference, otherwise a copy that it does."
  parameters := ["a"]
  body := [
    .branch (exclusive "a") [.give "a"] [],
    .call none "refuse_copy_of_linear" ["a"],
    .call (some "r") "copy_sarray" ["a", capacityOf "a"],
    .give "r"]

def bytePush : Function where
  name := "lean_byte_array_push"
  seen := some { result := object, parameters := [object, "uint8_t"] }
  parameters := ["a", "b"]
  body := [
    .call (some "least") "add_checked" [sizeOf "a", 1],
    .call (some "r") "sarray_with_capacity" ["a", "least", 0],
    .call (some "r") "sarray_exclusive" ["r"],
    .set "size" (sizeOf "r"),
    .storePart 1 ("r" + 24 + "size") "b",
    .store ("r" + 8) ("size" + 1),
    .give "r"]

def copySlice : Function where
  name := "lean_byte_array_copy_slice"
  about := "`ByteArray.copySlice`: `len` bytes of `src` from `src_off` written over `dest` from `dest_off`, extending\n`dest` if they run past its end. Offsets and lengths past the ends are clamped the way Lean specifies. The\nthree numbers are the caller's to give away; they are small unless someone passes 2^63 or more."
  seen := some { result := object, parameters := [object, object, object, object, object, "bool"] }
  parameters := ["src", "o_src_off", "dest", "o_dest_off", "o_len", "exact"]
  body := [
    .set "src_size" (sizeOf "src"),
    .set "dest_size" (sizeOf "dest"),
    .callOther (some "src_off") "rt_nat_to_size" ["o_src_off"],
    .callOther (some "len") "rt_nat_to_size" ["o_len"],
    .callOther (some "dest_off") "rt_nat_to_size" ["o_dest_off"],
    drop "o_src_off", drop "o_len", drop "o_dest_off",
    .branch (Expr.lt "src_size" "src_off") [.give "dest"] [],
    .branch (Expr.lt ("src_size" - "src_off") "len") [.set "len" ("src_size" - "src_off")] [],
    .branch (Expr.lt "dest_size" "dest_off") [.set "dest_off" "dest_size"] [],
    .call (some "new_size") "add_checked" ["dest_off", "len"],
    .branch (Expr.lt "new_size" "dest_size") [.set "new_size" "dest_size"] [],
    .call (some "r") "sarray_with_capacity" ["dest", "new_size", "exact"],
    .call (some "r") "sarray_exclusive" ["r"],
    .store ("r" + 8) "new_size",
    -- `r` is held by no one else, so it cannot be `src` and the ranges cannot overlap.
    copyBytes ("r" + 24 + "dest_off") ("src" + 24 + "src_off") "len",
    .give "r"]

def replicate : Function where
  name := "lean_mk_array"
  about := "`Array.replicate`: `n` references to `v`. Gives up both."
  seen := some { result := object, parameters := [object, object] }
  parameters := ["n", "v"]
  body := [
    .callOther (some "size") "rt_nat_to_size" ["n"],
    drop "n",
    .call (some "r") "array_new" ["size", "size"],
    .set "i" 0,
    .loop (Expr.lt "i" "size") [.store (slot "r" "i") "v", .set "i" ("i" + 1)],
    .branch (Expr.eq "size" 0) [drop "v"]
      [.branch (Expr.lt 1 "size") [.callOther none "lean_inc_n" ["v", "size" - 1]] []],
    .give "r"]

def outOfBounds : String := "lean_mk_string(\"Error: index out of bounds\")"

def exported : List Function := [
  { name := "lean_array_mk", seen := some { result := object, parameters := [object] }, parameters := ["list"],
    body := [.callOther (some "r") "lean_list_to_array" [1, "list"], .give "r"] },
  { name := "lean_array_to_list", seen := some { result := object, parameters := [object] }, parameters := ["a"],
    body := [.callOther (some "r") "lean_array_to_list_impl" [1, "a"], .give "r"] },
  copyExpand, copyExpandNonlinear, push, bytePush, copySlice, replicate,
  { name := "lean_array_get_panic"
    about := "`a[i]!` and `a.set! i v` with `i` out of bounds: a Lean panic, which here stops the machine."
    seen := some { result := object, parameters := [object] }, parameters := ["def_val"],
    body := [.outside (some "r") s!"lean_panic_fn((lean_object *)def_val, {outOfBounds})", .give "r"] },
  { name := "lean_array_set_panic", seen := some { result := object, parameters := [object, object] }
    parameters := ["a", "v"],
    body := [drop "v", .outside (some "r") s!"lean_panic_fn((lean_object *)a, {outOfBounds})", .give "r"] },
  { name := "lean_byte_array_mk"
    about := "`ByteArray.mk`: the bytes of an `Array UInt8`. Gives it up."
    seen := some { result := object, parameters := [object] }, parameters := ["a"],
    body := [
      .set "size" (sizeOf "a"),
      .call (some "r") "bytes_new" [1, "size", "size"],
      .set "i" 0,
      .loop (Expr.lt "i" "size") [
        .storePart 1 ("r" + 24 + "i") (Expr.shr (.load (slot "a" "i")) 1),
        .set "i" ("i" + 1)],
      drop "a",
      .give "r"] },
  { name := "lean_byte_array_data"
    about := "`ByteArray.data`: the bytes as an `Array UInt8`. Gives it up."
    seen := some { result := object, parameters := [object] }, parameters := ["a"],
    body := [
      .set "size" (sizeOf "a"),
      .call (some "r") "array_new" ["size", "size"],
      .set "i" 0,
      .loop (Expr.lt "i" "size") [
        .store (slot "r" "i") (Expr.or (Expr.shl (.part 1 ("a" + 24 + "i")) 1) 1),
        .set "i" ("i" + 1)],
      drop "a",
      .give "r"] },
  { name := "lean_byte_array_hash", seen := some { result := "uint64_t", parameters := [object] }, parameters := ["a"],
    body := [.callOther (some "r") "rt_hash_bytes" ["a" + 24, sizeOf "a", 11], .give "r"] },
  { name := "lean_sarray_eq_cold"
    about := "Equality of two scalar arrays already known to have the same number of elements."
    seen := some { result := "bool", parameters := [object, object] }, parameters := ["a1", "a2"],
    body := [
      .callOther (some "differ") "memcmp" ["a1" + 24, "a2" + 24, widthOf "a1" * sizeOf "a1"],
      .give (Expr.eq "differ" 0)] },
  { name := "lean_copy_sarray_nonlinear"
    about := "A copy of a scalar array someone else also holds, which compiled Lean asks for before changing it."
    seen := some { result := object, parameters := [object, "size_t"] }, parameters := ["a", "capacity"],
    body := [
      .call none "refuse_copy_of_linear" ["a"],
      .call (some "r") "copy_sarray" ["a", "capacity"],
      .give "r"] }]

def program : Program where
  about := "Arrays and byte arrays."
  preamble := "#include \"rt.h\"\n\n/* Init's own conversions between lists and arrays, compiled Lean that the runtime calls back into. */\nlean_object * lean_list_to_array(lean_object * type, lean_object * list);\nlean_object * lean_array_to_list_impl(lean_object * type, lean_object * array);\n"
  globals := []
  arrays := []
  others := [
    ("lean_alloc_object", { result := object, parameters := ["size_t"] }),
    ("lean_free_object", { result := "void", parameters := [object] }),
    ("lean_dec", { result := "void", parameters := [object] }),
    ("lean_inc", { result := "void", parameters := [object] }),
    ("lean_inc_n", { result := "void", parameters := [object, "size_t"] }),
    ("memcpy", { result := "void *", parameters := ["void *", "void const *", "size_t"] }),
    ("memcmp", { result := "int", parameters := ["void const *", "void const *", "size_t"] }),
    ("rt_nat_to_size", { result := "size_t", parameters := [object] }),
    ("rt_hash_bytes", { result := "uint64_t", parameters := ["uint8_t const *", "size_t", "uint64_t"] }),
    ("lean_list_to_array", { result := object, parameters := [object, object] }),
    ("lean_array_to_list_impl", { result := object, parameters := [object, object] })]
  functions := Checked.functions ++ [refuse, arrayNew, bytesNew, copyBytesArray, withCapacity, madeExclusive] ++ exported

end Mini.Array
