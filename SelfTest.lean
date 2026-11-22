/-! # The runtime self-test

One pure function that puts the runtime through its paces and returns what happened as text: strings and
their UTF-8 positions, arrays, byte arrays, closures of every shape, lazy values, numbers at the edges of
their types, and structures deep enough that freeing them must not recurse.

Nothing here knows which runtime it is on. The transcript must come out byte for byte the same on Lean's own
runtime, on the minimal runtime as an ordinary process, and inside the enclave, where the `selftest` command
returns its digest. Numbers of 2^63 and above have their own, larger test (`BigTest.lean`); here they only
appear where a small computation happens to cross that line. -/

namespace SelfTest

/-- 64-bit FNV-1a: enough to tell two transcripts apart, and small enough to read. Not a secure hash. -/
def fnv1a (bytes : ByteArray) : UInt64 :=
  bytes.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001b3) 0xcbf29ce484222325

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `n` in hexadecimal, at least one digit. -/
def hex (n : Nat) : String :=
  let rec go (fuel n : Nat) (acc : List Char) : List Char :=
    match fuel with
    | 0 => acc
    | fuel + 1 => if n < 16 then hexDigit n :: acc else go fuel (n / 16) (hexDigit (n % 16) :: acc)
  String.ofList (go 80 n [])

def hexBytes (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ (if x < 16 then "0" else "") ++ hex x.toNat) ""

/-- The lines gathered so far. -/
abbrev Log := Array String

def note (log : Log) (name value : String) : Log := log.push (name ++ ": " ++ value)

/-! ## Strings -/

def strings (log : Log) : Log := Id.run do
  let mut log := log
  let ascii := "hello, world"
  let mixed := "aé中𝄞z"   -- characters of 1, 2, 3 and 4 bytes, then 1
  log := note log "length ascii" (toString ascii.length)
  log := note log "length mixed" (toString mixed.length)
  log := note log "bytes mixed" (hexBytes mixed.toUTF8)
  log := note log "utf8 size mixed" (toString mixed.utf8ByteSize)
  log := note log "append" (ascii ++ " / " ++ mixed)
  log := note log "push" ((ascii.push '!').push '中')
  log := note log "chars mixed" (toString (mixed.toList.map (·.toNat)))
  log := note log "from chars" (String.ofList [Char.ofNat 0x7a, Char.ofNat 0xe9, Char.ofNat 0x1d11e])
  log := note log "equal" (toString (ascii == "hello, world") ++ " " ++ toString (ascii == mixed))
  log := note log "less" (toString (decide (ascii < mixed)) ++ " " ++ toString (decide (mixed < ascii)))
  log := note log "hash ascii" (hex (hash ascii).toNat)
  log := note log "hash mixed" (hex (hash mixed).toNat)
  log := note log "hash empty" (hex (hash "").toNat)
  log := note log "numbers" (toString 0 ++ " " ++ toString 4294967296 ++ " " ++ toString (-17 : Int))
  -- A string held twice must be copied before it is changed.
  let shared := ascii
  let grown := shared ++ "!"
  log := note log "shared kept" (shared ++ " | " ++ grown)
  -- Growing a string a piece at a time.
  let mut long := ""
  for i in [0:2000] do
    long := long ++ toString (i % 10)
  log := note log "long" (toString long.length ++ " " ++ hex (hash long).toNat)
  log := note log "split" (toString (("a,b,,c".splitOn ",").map (·.length)))
  log := note log "contains" (toString (ascii.toList.contains 'w') ++ " " ++ toString (ascii.toList.contains 'q'))
  log := note log "take drop" (toString (mixed.toList.take 2 |>.map (·.toNat)) ++ " " ++
    toString (mixed.toList.drop 3 |>.map (·.toNat)))
  return log

/-! ## Arrays -/

def arrays (log : Log) : Log := Id.run do
  let mut log := log
  let mut a : Array Nat := #[]
  for i in [0:100000] do
    a := a.push (i * i % 1000003)
  log := note log "array size" (toString a.size)
  log := note log "array sum" (toString (a.foldl (· + ·) 0))
  log := note log "array ends" (toString a[0]! ++ " " ++ toString a[99999]!)
  -- An array held twice must be copied before it is changed.
  let before := a
  a := a.set! 5 77
  log := note log "copy on write" (toString before[5]! ++ " " ++ toString a[5]!)
  let small := #[3, 1, 2]
  log := note log "to list" (toString small.toList)
  log := note log "of list" (toString [9, 8, 7].toArray)
  log := note log "replicate" (toString (Array.replicate 4 "x"))
  log := note log "replicate none" (toString (Array.replicate 0 "x").size)
  log := note log "pop" (toString small.pop)
  log := note log "reverse" (toString small.reverse)
  log := note log "map filter" (toString ((small.map (· * 10)).filter (· > 10)))
  log := note log "append" (toString (small ++ small))
  log := note log "nested" (toString #[#[1], #[], #[2, 3]])
  log := note log "sorted" (toString (#[5, 3, 9, 1, 7].qsort (· < ·)))
  log := note log "strings" (toString (#["b", "a"].push "c"))
  log := note log "extract" (toString (a.extract 2 6))
  log := note log "any all" (toString (small.any (· > 2)) ++ " " ++ toString (small.all (· > 2)))
  return log

/-! ## Byte arrays -/

def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

def byteArrays (log : Log) : Log := Id.run do
  let mut log := log
  let a := bytes [1, 2, 3, 4, 5]
  let b := bytes [0xAA, 0xBB, 0xCC]
  log := note log "bytes" (hexBytes a)
  log := note log "append" (hexBytes (a ++ b))
  log := note log "push" (hexBytes (a.push 6))
  log := note log "extract" (hexBytes (a.extract 1 4) ++ " " ++ hexBytes (a.extract 3 99) ++ " [" ++
    hexBytes (a.extract 4 2) ++ "] [" ++ hexBytes (a.extract 9 12) ++ "]")
  -- `copySlice` with every kind of offset: inside, running past the end, starting past the end.
  log := note log "copy inside" (hexBytes (b.copySlice 0 a 1 3))
  log := note log "copy past end" (hexBytes (b.copySlice 1 a 4 2))
  log := note log "copy from past end" (hexBytes (b.copySlice 7 a 0 2))
  log := note log "copy to past end" (hexBytes (b.copySlice 0 a 9 2))
  log := note log "copy long" (hexBytes (b.copySlice 0 a 0 99))
  log := note log "copy none" (hexBytes (b.copySlice 0 a 2 0))
  log := note log "set" (hexBytes (a.set! 2 0xFF))
  log := note log "shared kept" (hexBytes a)
  log := note log "to list" (toString a.toList)
  log := note log "data" (toString a.data)
  log := note log "hash" (hex (hash a).toNat ++ " " ++ hex (hash ByteArray.empty).toNat)
  log := note log "equal" (toString (a == bytes [1, 2, 3, 4, 5]) ++ " " ++ toString (a == b))
  let mut big := ByteArray.empty
  for i in [0:70000] do
    big := big.push (UInt8.ofNat (i * 7))
  log := note log "big" (toString big.size ++ " " ++ hex (fnv1a big).toNat)
  log := note log "big pieces" (hex (fnv1a (big.extract 100 60000 ++ big.extract 0 5)).toNat)
  return log

/-! ## Closures -/

def add3 (a b c : Nat) : Nat := a + 2 * b + 3 * c

def many (a b c d e f g h i j k l m n o p q r : Nat) : Nat :=
  a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g + 8 * h + 9 * i + 10 * j + 11 * k + 12 * l + 13 * m +
    14 * n + 15 * o + 16 * p + 17 * q + 18 * r

def twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)

def compose (fs : List (Nat → Nat)) (x : Nat) : Nat := fs.foldl (fun acc f => f acc) x

/-- Hides a value from the compiler, so that calls through it are real closure calls. -/
@[noinline] def opaqueId {α : Type} (x : α) : α := x

def closures (log : Log) : Log := Id.run do
  let mut log := log
  let f1 := opaqueId (add3 1)
  let f2 := opaqueId (f1 2)
  log := note log "partial" (toString (f2 3) ++ " " ++ toString (f1 5 7))
  let g := opaqueId many
  let g5 := opaqueId (g 1 2 3 4 5)
  let g17 := opaqueId (g5 6 7 8 9 10 11 12 13 14 15 16 17)
  log := note log "eighteen" (toString (g17 18) ++ " " ++ toString (g5 0 0 0 0 0 0 0 0 0 0 0 0 1))
  log := note log "twice" (toString (twice (opaqueId (· + 3)) 10) ++ " " ++ toString (twice (twice (· * 2)) 1))
  log := note log "compose" (toString (compose [(· + 1), (· * 5), opaqueId (add3 1 1)] 4))
  let adders := (Array.range 5).map fun i => opaqueId (fun x => x + i)
  log := note log "stored" (toString (adders.map (· 100)))
  -- A function that returns a function, applied to everything at once.
  let curried := opaqueId (fun (a : Nat) => opaqueId (fun (b : Nat) => opaqueId (fun (c : Nat) => a * 100 + b * 10 + c)))
  log := note log "curried" (toString (curried 1 2 3))
  let shared := opaqueId (add3 9)
  log := note log "shared" (toString (shared 1 1) ++ " " ++ toString (shared 2 2))
  return log

/-! ## Lazy values -/

def lazies (log : Log) : Log := Id.run do
  let mut log := log
  let t : Thunk Nat := Thunk.mk fun _ => (List.range 1000).foldl (· + ·) 0
  log := note log "thunk" (toString t.get ++ " " ++ toString t.get)
  let ts := (Array.range 4).map fun i => (Thunk.mk fun _ => i * i : Thunk Nat)
  log := note log "thunks" (toString (ts.map (·.get)))
  let chain : Thunk Nat := Thunk.mk fun _ => t.get + 1
  log := note log "chain" (toString chain.get)
  return log

/-! ## Numbers at the edges of their types -/

def numbers (log : Log) : Log := Id.run do
  let mut log := log
  let top : Nat := 9223372036854775807   -- 2^63 - 1, the largest number that is not a big number
  log := note log "nat" (toString (top - 1) ++ " " ++ toString (top / 3) ++ " " ++ toString (top % 1000))
  log := note log "nat sub" (toString (5 - 7) ++ " " ++ toString (top - top))
  log := note log "nat shift" (toString (1 <<< 62) ++ " " ++ toString (top >>> 61) ++ " " ++ toString (0 <<< 9))
  log := note log "nat bits" (toString (top &&& 0xFF0F) ++ " " ++ toString (0xF0 ||| 0x0F) ++ " " ++
    toString (0xFF ^^^ 0x0F))
  log := note log "nat pow" (toString (2 ^ 62) ++ " " ++ toString (3 ^ 39) ++ " " ++ toString (7 ^ 0))
  log := note log "nat log2" (toString (Nat.log2 1) ++ " " ++ toString (Nat.log2 1023) ++ " " ++
    toString (Nat.log2 top))
  log := note log "nat cross" (toString (top + 1) ++ " " ++ toString (top * 2) ++ " " ++ toString (2 ^ 64))
  log := note log "u8" (toString ((250 : UInt8) + 10) ++ " " ++ toString ((3 : UInt8) - 5) ++ " " ++
    toString ((200 : UInt8) * 3))
  log := note log "u16" (toString ((65535 : UInt16) + 1) ++ " " ++ toString ((1 : UInt16) <<< 15))
  log := note log "u32" (toString ((4294967295 : UInt32) + 2) ++ " " ++ toString ((7 : UInt32) / 2))
  log := note log "u64" (toString ((18446744073709551615 : UInt64) + 2) ++ " " ++
    toString ((1 : UInt64) <<< 63) ++ " " ++ toString ((0xFFFFFFFFFFFFFFFF : UInt64) * 3))
  log := note log "u64 to nat" (toString (18446744073709551615 : UInt64).toNat)
  log := note log "of nat" (toString (UInt8.ofNat 513) ++ " " ++ toString (UInt32.ofNat (2 ^ 40 + 5)) ++ " " ++
    toString (UInt64.ofNat (2 ^ 64 + 9)))
  log := note log "int" (toString ((-7 : Int) / 2) ++ " " ++ toString ((-7 : Int) % 2) ++ " " ++
    toString ((7 : Int) / (-2)) ++ " " ++ toString ((7 : Int) % (-2)))
  log := note log "int edge" (toString ((2147483647 : Int) + 1) ++ " " ++ toString ((-2147483648 : Int) - 1) ++
    " " ++ toString ((2147483647 : Int) * 2147483647))
  log := note log "int nat" (toString (Int.toNat (-5)) ++ " " ++ toString (Int.natAbs (-5)) ++ " " ++
    toString ((5 : Int) - 9))
  log := note log "compare" (toString (decide (top < top + 1)) ++ " " ++ toString (decide ((-1 : Int) < 0)) ++
    " " ++ toString (compare 3 5 == .lt) ++ " " ++ toString (max 3 5) ++ " " ++ toString (min top 4))
  return log

/-! ## Structures that are deep or wide -/

inductive Tree where
  | leaf (value : Nat)
  | node (left right : Tree)

def Tree.build : Nat → Nat → Tree
  | 0, seed => .leaf seed
  | depth + 1, seed => .node (build depth (2 * seed)) (build depth (2 * seed + 1))

def Tree.sum : Tree → Nat
  | .leaf value => value
  | .node left right => left.sum + right.sum

/-- A list as long as asked, built without recursion that deep. -/
def longList (n : Nat) : List Nat := Id.run do
  let mut list := []
  for i in [0:n] do
    list := i :: list
  return list

def structures (log : Log) : Log := Id.run do
  let mut log := log
  -- A million cells in one chain: freeing it one call per cell would overflow any stack.
  let list := longList 1000000
  log := note log "long list" (toString list.length ++ " " ++ toString (list.foldl (· + ·) 0))
  let tree := Tree.build 16 1
  log := note log "tree" (toString tree.sum)
  let pairs := (List.range 1000).map fun i => (i, toString i, some (i % 3))
  log := note log "pairs" (toString (pairs.foldl (fun acc (i, s, o) => acc + i + s.length + o.getD 0) 0))
  let options : List (Option (Option Nat)) := [none, some none, some (some 3)]
  log := note log "options" (toString options)
  let result : Except String Nat := do
    let a ← pure 5
    if a > 3 then throw "too large" else pure a
  log := note log "except" (match result with | .ok v => toString v | .error e => e)
  let sums := (List.range 200).map fun i => (longList (i * 10)).length
  log := note log "many lists" (toString (sums.foldl (· + ·) 0))
  return log

/-- Everything, as lines of text. -/
def lines : Array String :=
  #[] |> strings |> arrays |> byteArrays |> closures |> lazies |> numbers |> structures

/-- Everything, as the bytes the transcript is compared by. -/
def transcript : ByteArray :=
  lines.foldl (fun out line => out ++ line.toUTF8 ++ "\n".toUTF8) ByteArray.empty

/-- The digest the `selftest` command returns: eight bytes, big-endian. -/
def digest : ByteArray :=
  let h := fnv1a transcript
  (List.range 8).foldl (fun out i => out.push (h >>> (56 - 8 * i).toUInt64).toUInt8) ByteArray.empty

end SelfTest
