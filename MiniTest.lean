import Mini.Run
import Mini.Alloc
import Mini.Hash
import MiniStringTest
import Mini.Secret
import Mini.Constant
import Mini.String
import Mini.Array
import Mini.Checked

/-! Runs the allocator, hash, secret, checked arithmetic, and strings as `Mini` defines them, with no C involved. -/

open Mini

def base : UInt64 := 0x100000
def heapSize : UInt64 := 0x100000

def outside : Outside := fun c _ s =>
  if c.startsWith "silo_plat_heap" then pure (base, { s with globals := put s.globals "heap_size" heapSize })
  else throw c

def call (function : String) (argument : UInt64) (s : State) : Except String (Ending × State) :=
  Alloc.program.call outside 100000 function [argument] s

def malloc (size : UInt64) (s : State) : Except String (UInt64 × State) := do
  match ← call "rt_malloc" size s with
  | (.gave block, s) => pure (block, s)
  | (.stopped why, _) => throw s!"stopped: {why}"
  | (.on, _) => throw "rt_malloc gave nothing"

def free (block : UInt64) (s : State) : Except String State := do
  match ← call "rt_free" block s with
  | (.stopped why, _) => throw s!"stopped: {why}"
  | (_, s) => pure s

def scenario : Except String (List (String × Bool)) := do
  let s := Alloc.program.start
  let (a, s) ← malloc 1 s
  let (b, s) ← malloc 1 s
  let s := { s with memory := writeBytes (writeBytes s.memory a 0xDEAD 8) (a + 8) 0xBEEF 8 }
  let s ← free a s
  let wiped := (readBytes s.memory a 8).toOption == some 0 && (readBytes s.memory (a + 8) 8).toOption == some 0
  let (again, s) ← malloc 16 s
  let twice := match free b s >>= free b with
    | .error why => why == "stopped: a block was freed that is not in use"
    | .ok _ => false
  let (large, s) ← malloc 5000 s
  let tooMuch := match malloc 0x200000 s with
    | .error why => why == "lean_internal_panic_out_of_memory()"
    | .ok _ => false
  let mut state := s
  let mut live : Array (UInt64 × UInt64) := #[]
  let mut apart := true
  let mut seed : UInt64 := 12345
  for _ in [0:300] do
    seed := seed * 6364136223846793005 + 1442695040888963407
    let size := (seed >>> 33) % 600 + 1
    if (seed >>> 20) % 3 == 0 && live.size > 0 then
      let i := ((seed >>> 40) % live.size.toUInt64).toNat
      state ← free live[i]!.1 state
      live := live.eraseIdx! i
    else
      let (block, next) ← malloc size state
      state := next
      apart := apart && live.all fun (other, length) => block + size ≤ other || other + length ≤ block
      live := live.push (block, size)
  return [
    ("the first block starts after its header", a == base + 16),
    ("the next block does not overlap it", b == a + 32),
    ("a freed block is zeroed", wiped),
    ("and is the next one handed out for that size", again == a),
    ("freeing a block twice stops the machine", twice),
    ("a large block records its class", (readBytes state.memory (large - 16) 8).toOption == some 257),
    ("asking for more than there is ends in out of memory", tooMuch),
    ("300 requests and frees: no two blocks in use overlap", apart)]

def hashAgrees : Bool := Id.run do
  let mut agrees := true
  for length in [0:41] do
    let bytes := ByteArray.mk ((Array.range length).map fun i => (i * 37 + 11).toUInt8)
    let mut memory : UInt64 → Option UInt8 := fun _ => none
    for i in [0:length] do
      memory := put memory (4096 + i.toUInt64) (some bytes[i]!)
    let ran := Hash.program.call (fun c _ _ => throw c) 10000 "rt_hash_bytes" [4096, length.toUInt64, 11]
      { memory := memory }
    match ran with
    | .ok (.gave value, _) => agrees := agrees && value == hash bytes
    | _ => agrees := false
  return agrees

def secretChecks : List (String × Bool) := Id.run do
  let ran (f : String) (args : List UInt64) (s : State) : Option UInt64 :=
    match Secret.program.call (fun c _ _ => throw c) 100000 f args s with
    | .ok (.gave v, _) => some v
    | _ => none
  let mut equal := true
  for (a, b) in [("abcdefgh", "abcdefgh"), ("abcdefgh", "abcdefgx"), ("abcdefgh", "xbcdefgh"), ("", ""),
      ("\x00\xff", "\x00\xff"), ("\x00\xff", "\x00\xfe")] do
    let (x, y) := (a.toUTF8, b.toUTF8)
    let mut memory : UInt64 → Option UInt8 := fun _ => none
    for i in [0:x.size] do memory := put memory (0x1000 + 24 + i.toUInt64) (some x[i]!)
    for i in [0:y.size] do memory := put memory (0x2000 + 24 + i.toUInt64) (some y[i]!)
    for n in [0:x.size + 1] do
      let same := (x.extract 0 n).toList == (y.extract 0 n).toList
      equal := equal && ran "silo_secret_equal" [0x1000, 0x2000, n.toUInt64] { memory } == some (if same then 1 else 0)
  let select := [(1, 7, 9, 7), (0, 7, 9, 9), (1, 0xFFFFFFFFFFFFFFFF, 0, 0xFFFFFFFFFFFFFFFF), (0, 0, 5, 5)].all
    fun (bit, x, y, want) => ran "silo_secret_select" [bit, x, y] {} == some want
  let passes := Secret.secrets.all fun (name, secret) =>
    match Secret.program.functions.find? (·.name == name) with
    | some f => (Constant.check f secret).isOk
    | none => false
  let early : Function := { name := "early", parameters := ["a", "b", "n"], body := [
    .set "i" 0,
    .loop (Expr.lt "i" "n") [
      .branch (Expr.ne (.part 1 ("a" + "i")) (.part 1 ("b" + "i"))) [.give 0] [],
      .set "i" ("i" + 1)],
    .give 1] }
  let lookup : Function := { name := "lookup", parameters := ["table", "k"], body := [.give (.load ("table" + "k" * 8))] }
  let refused := !(Constant.check early []).isOk && !(Constant.check lookup ["k"]).isOk
    && (match Str.program.functions.find? (·.name == "lean_string_eq_cold") with
        | some f => !(Constant.check f []).isOk
        | none => false)
  let edges : List UInt64 := [0, 1, 2, 7, 8, 9, 255, 256, 0x7FFFFFFFFFFFFFFE, 0x7FFFFFFFFFFFFFFF, 0x8000000000000000]
  let masked := edges.all fun i => edges.all fun n =>
    let f : Function := { name := "f", parameters := ["i", "n"], body := Stmt.inBounds "i" "n" ++ [.give "i"] }
    let p : Program := { about := "", preamble := "", globals := [], arrays := [], functions := [f] }
    let ran := match p.call (fun c _ _ => throw c) 100 "f" [i, n] {} with
      | .ok (.gave v, _) => some v
      | _ => none
    i ≥ 0x8000000000000000 || n > 0x8000000000000000 || ran == some (if i < n then i else 0)
  return [
    ("an index past a bounds check, masked: itself below the size, zero at or above it", masked),
    ("secret equal: the same as comparing, for every length of six pairs", equal),
    ("secret select: chooses by the bit", select),
    ("secret equal and select: no secret decides a branch, an address or a division", passes),
    ("the check refuses an early exit, a secret address, and the strings' own equality (memcmp)", refused)]

def checkedChecks : List (String × Bool) :=
  let ran (f : String) (a b : UInt64) : Option UInt64 :=
    match Array.program.call (fun c _ _ => throw c) 1000 f [a, b] {} with
    | .ok (.gave v, _) => some v
    | _ => none
  let stops (f : String) (a b : UInt64) : Bool :=
    match Array.program.call (fun c _ _ => throw c) 1000 f [a, b] {} with
    | .ok (.stopped _, _) => true
    | _ => false
  let big : UInt64 := 0xFFFFFFFFFFFFFFFF
  [("checked sums: right below the top, and stop above it",
      ran "add_checked" 3 4 == some 7 && ran "add_checked" (big - 1) 1 == some big && stops "add_checked" big 1
        && stops "add_checked" (big / 2 + 1) (big / 2 + 1)),
   ("checked products: right below the top, and stop above it",
      ran "mul_checked" 6 7 == some 42 && ran "mul_checked" 0 big == some 0 && ran "mul_checked" big 1 == some big
        && ran "mul_checked" 0x100000000 0xFFFFFFFF == some 0xFFFFFFFF00000000
        && stops "mul_checked" 0x100000000 0x100000000 && stops "mul_checked" big 2)]

def main : IO UInt32 := do
  match scenario with
  | .error why =>
    IO.println s!"FAIL  the allocator failed as the language defines it: {why}"
    return 1
  | .ok checks =>
    let mut failures := 0
    for (name, held) in checks ++ [("the byte hash gives what Lean's own gives, for 41 lengths", hashAgrees)] do
      IO.println s!"{if held then "ok   " else "FAIL "} {name}"
      if !held then failures := failures + 1
    for (name, held) in secretChecks ++ checkedChecks do
      IO.println s!"{if held then "ok   " else "FAIL "} {name}"
      if !held then failures := failures + 1
    for (name, check) in StringTest.checks do
      match check with
      | .ok () => IO.println s!"ok    strings: {name}"
      | .error why => IO.println s!"FAIL  strings: {name}: {why}"; failures := failures + 1
    if failures == 0 then IO.println "mini-test: all checks passed" else IO.println s!"mini-test: {failures} failed"
    return (if failures == 0 then 0 else 1)
