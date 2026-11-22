import Mini.Lang

/-! # The allocator

The runtime's allocator. Its C is printed when the runtime is built (`scripts/print-runtime`). -/

namespace Mini.Alloc

/-- Blocks up to 4096 bytes come in multiples of 16: class `c` holds blocks of `c * 16` bytes. -/
def smallClasses : Nat := 4096 / 16 + 1
/-- Above that they are powers of two, from 2^13 to 2^47. -/
def largeFirst : Nat := 13
def largeLast : Nat := 47
/-- What a block's second header word says while it is in use, and once it is freed. -/
def inUse : Nat := 0xA110CA7EDB10C000
def freed : Nat := 0xF4EEDB10C0000000

def small : Expr := .lit (UInt64.ofNat smallClasses)
def first : Expr := .lit (UInt64.ofNat largeFirst)
def outOfMemory : Stmt := .outside none "lean_internal_panic_out_of_memory()"

def classBytes : Function where
  name := "class_bytes"
  about := "How many bytes a block of this class holds."
  parameters := ["size_class"]
  body := [
    .branch (Expr.lt "size_class" small) [.give ("size_class" * 16)] [],
    .give (Expr.shl 1 (first + ("size_class" - small)))]

def listGet : Function where
  name := "list_get"
  about := "The first free block of this class, or zero."
  parameters := ["size_class"]
  body := [
    .branch (Expr.lt "size_class" small) [.give (.item "free_small" "size_class")] [],
    .give (.item "free_large" ("size_class" - small))]

def listSet : Function where
  name := "list_set"
  parameters := ["size_class", "block"]
  body := [
    .branch (Expr.lt "size_class" small) [.setItem "free_small" "size_class" "block"]
      [.setItem "free_large" ("size_class" - small) "block"]]

def malloc : Function where
  name := "rt_malloc"
  about := "A block of at least `size` bytes. Sixteen bytes in front of it record its class and its state."
  seen := some { result := "void *", parameters := ["size_t"] }
  parameters := ["size"]
  body := [
    .branch (Expr.eq "size" 0) [.set "size" 1] [],
    .branch (Expr.le "size" 4096)
      [.set "size_class" (("size" + 15) / 16)]
      [.set "log2" first,
       .loop (Expr.lt (Expr.shl 1 "log2") "size") [
         .set "log2" ("log2" + 1),
         .branch (Expr.lt (.lit (UInt64.ofNat largeLast)) "log2") [outOfMemory] []],
       .set "size_class" (small + ("log2" - first))],
    .call (some "block") "list_get" ["size_class"],
    .branch (Expr.ne "block" 0)
      [.call none "list_set" ["size_class", .load "block"],
       .store "block" 0,
       .set "header" ("block" - 16),
       .branch (Expr.ne (.load ("header" + 8)) (.lit (UInt64.ofNat freed)))
         [.stop "the allocator's free list holds a block that is not free"] []]
      [.branch (Expr.eq (.global "heap_asked") 0)
         [.outside (some "start") "silo_plat_heap((size_t *)&heap_size)",
          .setGlobal "heap_at" "start",
          .branch (Expr.eq "start" 0) [.setGlobal "heap_end" 0]
            [.setGlobal "heap_end" ("start" + .global "heap_size")],
          .setGlobal "heap_asked" 1,
          -- Objects waiting to be freed are linked through 48 bits of their headers (object.c).
          .branch (Expr.ne (Expr.shr (.global "heap_end") 48) 0)
            [.stop "the heap lies above what 48-bit object links can reach"] []] [],
       .call (some "bytes") "class_bytes" ["size_class"],
       .set "needed" (16 + "bytes"),
       .branch (Expr.or (Expr.eq (.global "heap_at") 0) (Expr.lt (.global "heap_end" - .global "heap_at") "needed"))
         [outOfMemory] [],
       .set "header" (.global "heap_at"),
       .setGlobal "heap_at" (.global "heap_at" + "needed"),
       .store "header" "size_class"],
    .store ("header" + 8) (.lit (UInt64.ofNat inUse)),
    .give ("header" + 16)]

def free : Function where
  name := "rt_free"
  about := "Takes a block back. It is zeroed, so nothing a Lean value held outlives the value on the heap."
  seen := some { result := "void", parameters := ["void *"] }
  parameters := ["block"]
  body := [
    .set "header" ("block" - 16),
    .branch (Expr.ne (.load ("header" + 8)) (.lit (UInt64.ofNat inUse)))
      [.stop "a block was freed that is not in use"] [],
    .store ("header" + 8) (.lit (UInt64.ofNat freed)),
    .set "size_class" (.load "header"),
    .call (some "bytes") "class_bytes" ["size_class"],
    .set "at" 0,
    .loop (Expr.lt "at" "bytes") [.store ("block" + "at") 0, .set "at" ("at" + 8)],
    -- A compiler may drop stores nothing reads, and could come to see these that way: the block goes on a
    -- list, and a later request gets it zeroed anyway. Not dropping them is the point.
    .keep "block",
    .call (some "next") "list_get" ["size_class"],
    .store "block" "next",
    .call none "list_set" ["size_class", "block"]]

def program : Program where
  about := "Allocation.

One region from the platform, handed out from the front and never returned. A freed block goes on a list for
its size and is reused for the next request of that size:

  - up to 4096 bytes, sizes are multiples of 16, one list each;
  - above that, sizes are powers of two, one list each.

Every block is zeroed when it is freed, so nothing a Lean value held (a key, a nonce) outlives the value on
the heap. Sixteen bytes in front of each block record its size class and whether it is in use; freeing a
block that is not in use stops the machine instead of corrupting the lists.

Which block a request gets depends only on the sizes asked for and freed so far, never on what the blocks
contain."
  preamble := "#include \"rt.h\"\n"
  globals := ["heap_at", "heap_end", "heap_asked", "heap_size"]
  arrays := [("free_small", smallClasses), ("free_large", largeLast - largeFirst + 1)]
  functions := [classBytes, listGet, listSet, malloc, free]

end Mini.Alloc
