import Mini.Run
import Mini.String
import Runtime.Utf8

/-! The string program run as the language defines it, with no C involved, against Lean's own strings.

Everything outside the program is played here: objects are handed out one after another with a gap of 64
bytes after each, and freeing one forgets its bytes. So besides failing on its own if the program reads a
byte nothing has written (past a string's end, in room not yet used, in a freed object), a run is checked
afterwards for any byte written into a gap or into an object after it was freed. -/

namespace StringTest
open Mini

def firstObject : UInt64 := 0x200000

/-- Objects as start and size, in pairs; freed ones in `freed`. -/
def objects (s : State) : Array UInt64 := (s.arrays "objects").getD #[]
def freedOnes (s : State) : Array UInt64 := (s.arrays "freed").getD #[]

def allocate (n : UInt64) (s : State) : UInt64 × State :=
  let start := if s.globals "next" == 0 then firstObject else s.globals "next"
  let next := (start + n + 64 + 15) &&& ~~~15
  (start, { s with globals := put s.globals "next" next,
                   arrays := put s.arrays "objects" (some (((objects s).push start).push n)) })

def setWord (s : State) (address value : UInt64) : State := { s with memory := writeBytes s.memory address value 8 }
def setByte (s : State) (address : UInt64) (b : UInt8) : State := { s with memory := put s.memory address (some b) }
def word (s : State) (address : UInt64) : Except String UInt64 := readBytes s.memory address 8
def byte (s : State) (address : UInt64) : Except String UInt8 := do
  match s.memory address with
  | some b => pure b
  | none => throw s!"a read at {address}, which nothing has written"

def sizeOfObject (s : State) (o : UInt64) : Option UInt64 := Id.run do
  let all := objects s
  for i in [0:all.size / 2] do
    if all[2 * i]! == o then return some all[2 * i + 1]!
  return none

def release (o : UInt64) (s : State) : Except String State := do
  let all := objects s
  let some i := (List.range (all.size / 2)).find? (all[2 * · ]! == o)
    | throw s!"{o} was freed, and is not an object in use"
  let n := all[2 * i + 1]!
  let mut memory := s.memory
  for k in [0:n.toNat] do memory := put memory (o + k.toUInt64) none
  let all := (all.set! (2 * i) 0).set! (2 * i + 1) 0
  let arrays := put (put s.arrays "objects" (some all)) "freed" (some (((freedOnes s).push o).push n))
  pure { s with memory := memory, arrays := arrays }

def decRef (o : UInt64) (s : State) : Except String State := do
  let header ← word s o
  let count := header &&& 0xFFFFFFFF
  if count == 1 then release o s
  else if count == 0 then pure s
  else pure (setWord s o (header - 1))

def outside : Outside := fun c arguments s => do
  match c, arguments with
  | "lean_alloc_object", [n] => pure (allocate n s)
  | "lean_alloc_ctor", [tag, objs, scalars] =>
    let (o, s) := allocate (8 + 8 * objs + scalars) s
    pure (o, setWord s o ((1 : UInt64) ||| (objs <<< 48) ||| (tag <<< 56)))
  | "lean_alloc_sarray", [width, size, capacity] =>
    let (o, s) := allocate (24 + width * capacity) s
    pure (o, setWord (setWord (setWord s o ((1 : UInt64) ||| (width <<< 48) ||| ((248 : UInt64) <<< 56))) (o + 8) size) (o + 16) capacity)
  | "lean_free_object", [o] => pure (0, ← release o s)
  | "lean_dec_ref", [o] => pure (0, ← decRef o s)
  | "lean_dec", [o] => if o &&& 1 == 1 then pure (0, s) else pure (0, ← decRef o s)
  | "lean_usize_add_checked", [a, b] => if a + b < a then throw "an overflow in lean_usize_add_checked" else pure (a + b, s)
  | "lean_usize_mul_checked", [a, b] =>
    if a.toNat * b.toNat ≥ 2 ^ 64 then throw "an overflow in lean_usize_mul_checked" else pure (a * b, s)
  | "lean_usize_to_nat", [n] => if n < 2 ^ 63 then pure ((n <<< 1) ||| 1, s) else throw "a big number"
  | "memcpy", [to, from_, n] =>
    if n != 0 && to < from_ + n && from_ < to + n then throw "memcpy of ranges that overlap" else
    let mut s := s
    for k in [0:n.toNat] do s := setByte s (to + k.toUInt64) (← byte s (from_ + k.toUInt64))
    pure (to, s)
  | "memcmp", [a, b, n] =>
    for k in [0:n.toNat] do
      let x ← byte s (a + k.toUInt64)
      let y ← byte s (b + k.toUInt64)
      if x < y then return (0xFFFFFFFFFFFFFFFF, s)
      if y < x then return (1, s)
    pure (0, s)
  | "strlen", [p] =>
    let mut n : UInt64 := 0
    for _ in [0:100000] do
      if (← byte s (p + n)) == 0 then return (n, s)
      n := n + 1
    throw "strlen found no end"
  | "rt_hash_bytes", [p, n, 11] =>
    let mut bytes := ByteArray.empty
    for k in [0:n.toNat] do bytes := bytes.push (← byte s (p + k.toUInt64))
    pure (hash bytes, s)
  | "rt_utf8_strict", [b0, b1, b2, b3, available] =>
    pure ((Runtime.Utf8.strict b0.toUInt8 b1.toUInt8 b2.toUInt8 b3.toUInt8 available.toUSize).toUInt64, s)
  | "rt_utf8_read", [b0, b1, b2, b3, available] =>
    pure (Runtime.Utf8.read b0.toUInt8 b1.toUInt8 b2.toUInt8 b3.toUInt8 available.toUSize, s)
  | "rt_utf8_write", [c] => pure (Runtime.Utf8.write c.toUInt32, s)
  | "rt_utf8_claims", [c, most] => pure ((Runtime.Utf8.claims c.toUInt8 most.toUInt8).toUInt64, s)
  | _, _ => throw s!"nothing here plays {c} {arguments}"

/-- Nothing was written into a gap after an object, or into an object after it was freed. -/
def untouched (s : State) : Except String Unit := do
  let all := objects s ++ freedOnes s
  for i in [0:all.size / 2] do
    let start := all[2 * i]!
    let n := all[2 * i + 1]!
    if start == 0 then continue
    for k in [0:64] do
      if (s.memory (start + n + k.toUInt64)).isSome then throw s!"a write {k} bytes past the object at {start}"
  let freed := freedOnes s
  for i in [0:freed.size / 2] do
    for k in [0:freed[2 * i + 1]!.toNat] do
      if (s.memory (freed[2 * i]! + k.toUInt64)).isSome then throw s!"a write into the freed object at {freed[2 * i]!}"

/-- A string in memory, as Lean lays one out, held `count` times, with `extra` bytes of room nothing has written. -/
def place (str : String) (count : UInt64) (extra : Nat) (s : State) : UInt64 × State := Id.run do
  let bytes := str.toUTF8
  let size := bytes.size + 1
  let (o, s) := allocate (32 + (size + extra).toUInt64) s
  let mut s := setWord s o (count ||| ((249 : UInt64) <<< 56))
  s := setWord (setWord (setWord s (o + 8) size.toUInt64) (o + 16) (size + extra).toUInt64) (o + 24) str.length.toUInt64
  for i in [0:bytes.size] do s := setByte s (o + 32 + i.toUInt64) bytes[i]!
  return (o, setByte s (o + 32 + bytes.size.toUInt64) 0)

/-- The string at `o`, after checking it is laid out the way Lean expects. -/
def take (o : UInt64) (s : State) : Except String String := do
  if (← word s o) >>> 56 != 249 then throw s!"{o} is not a string"
  let size ← word s (o + 8)
  let capacity ← word s (o + 16)
  let length ← word s (o + 24)
  if size == 0 || capacity < size then throw s!"a string of {size} bytes with room for {capacity}"
  match sizeOfObject s o with
  | some n => if n < 32 + capacity then throw s!"a string with room for {capacity} bytes in {n}"
  | none => throw s!"{o} is not an object in use"
  let mut bytes := ByteArray.empty
  for k in [0:(size - 1).toNat] do bytes := bytes.push (← byte s (o + 32 + k.toUInt64))
  if (← byte s (o + 32 + size - 1)) != 0 then throw "no zero at the end"
  let some str := String.fromUTF8? bytes | throw "bytes that are not UTF-8"
  if str.length != length.toNat then throw s!"{length} characters said, {str.length} there"
  return str

def call (function : String) (arguments : List UInt64) (s : State) : Except String (UInt64 × State) := do
  match ← Str.program.call outside 1000000 function arguments s with
  | (.gave value, s) => untouched s; pure (value, s)
  | (.stopped why, _) => throw s!"stopped: {why}"
  | (.on, _) => throw s!"{function} gave nothing"

def box (n : Nat) : UInt64 := (n.toUInt64 <<< 1) ||| 1

/-- Short ones for every position, and ones long enough for the paths that take eight bytes at a time. -/
def samples : List String := ["", "a", "hello, world", "héllo wörld", "中文字", "𝄞x𝄞", "aé中𝄞",
  "abcdefghijklmnopqrstuvwxyz", "abcdefghijklmnopqrstuvwxyZ", "abcdefgh中ijklmnopqrstuvwxyz"]
def chars : List Char := ['!', 'é', '中', '𝄞']

/-- Each check is a name, and either nothing or what went wrong. -/
abbrev Check := Except String Unit

def expect (what : String) (got wanted : String) : Check :=
  if got == wanted then pure () else throw s!"{what}: {repr got}, where Lean gives {repr wanted}"

def appends : Check := do
  for a in samples do for b in samples do for count in [1, 2] do for extra in [0, 8] do
    let (x, s) := place a count extra {}
    let (y, s) := place b 1 0 s
    let (r, s) ← call "lean_string_append" [x, y] s
    expect s!"{repr a} ++ {repr b} (held {count}, room {extra})" (← take r s) (a ++ b)
    expect "what was appended, afterwards" (← take y s) b
    if count == 2 then expect "a string held twice, afterwards" (← take x s) a

def pushes : Check := do
  for a in samples do for c in chars do for count in [1, 2] do for extra in [0, 8] do
    let (x, s) := place a count extra {}
    let (r, s) ← call "lean_string_push" [x, c.toNat.toUInt64] s
    expect s!"{repr a}.push {repr c} (held {count}, room {extra})" (← take r s) (a.push c)
    if count == 2 then expect "a string held twice, afterwards" (← take x s) a

def positions : Check := do
  for a in samples do
    let (x, s) := place a 1 0 {}
    for i in [0:a.utf8ByteSize + 3] do
      let (got, _) ← call "lean_string_utf8_get" [x, box i] s
      let wanted := (String.Pos.Raw.get a ⟨i⟩).toNat
      if got.toNat != wanted then throw s!"get {repr a} {i}: {got}, where Lean gives {wanted}"
      let (next, _) ← call "lean_string_utf8_next" [x, box i] s
      let wanted := (String.Pos.Raw.next a ⟨i⟩).byteIdx
      if next != box wanted then throw s!"next {repr a} {i}: {next >>> 1}, where Lean gives {wanted}"
      -- The inline `String.get` and `String.next` call these for a byte that is not ASCII.
      if h : i < a.toUTF8.size then
        let c := a.toUTF8[i]
        if c ≥ 0x80 then
          let (got, _) ← call "lean_string_utf8_get_fast_cold" [x + 32, i.toUInt64, (a.utf8ByteSize + 1).toUInt64, c.toUInt64] s
          if got.toNat != (String.Pos.Raw.get a ⟨i⟩).toNat then throw s!"get_fast_cold {repr a} {i}"
          let (next, _) ← call "lean_string_utf8_next_fast_cold" [i.toUInt64, c.toUInt64] s
          if next != box (String.Pos.Raw.next a ⟨i⟩).byteIdx then throw s!"next_fast_cold {repr a} {i}"
    -- A position that is not a small number: an object nothing here has written, which must not be read.
    let (got, _) ← call "lean_string_utf8_get" [x, 0x7000000] s
    if got != 65 then throw s!"get at a big position: {got}"

def extracts : Check := do
  for a in samples do
    let (x, s) := place a 1 0 {}
    let ends := List.range (a.utf8ByteSize + 3)
    for b in ends do for e in ends do
      let (r, s) ← call "lean_string_utf8_extract" [x, box b, box e] s
      expect s!"extract {repr a} {b} {e}" (← take r s) (String.Pos.Raw.extract a ⟨b⟩ ⟨e⟩)
    let (r, s) ← call "lean_string_utf8_extract" [x, box 0, 0x7000000] s
    expect s!"extract {repr a} to a big position" (← take r s) (String.Pos.Raw.extract a ⟨0⟩ ⟨2 ^ 64⟩)

def lists : Check := do
  for a in samples do
    -- To a list of characters.
    let (x, s) := place a 1 0 {}
    let (l, s) ← call "lean_string_data" [x] s
    let mut at_ := l
    let mut got : List Nat := []
    for _ in [0:a.length + 1] do
      if at_ &&& 1 == 1 then break
      got := got ++ [((← word s (at_ + 8)) >>> 1).toNat]
      at_ ← word s (at_ + 16)
    if got != a.toList.map (·.toNat) then throw s!"data {repr a}: {got}"
    if (← sizeOfObject s x |>.isSome |> pure) then throw s!"data {repr a} kept the string it was given"
    -- And back.
    let (r, s) ← call "lean_string_mk" [l] s
    expect s!"mk of the characters of {repr a}" (← take r s) a

def bytesOut : Check := do
  for a in samples do
    let (x, s) := place a 1 0 {}
    let (r, s) ← call "lean_string_to_utf8" [x] s
    let size ← word s (r + 8)
    let mut got := ByteArray.empty
    for k in [0:size.toNat] do got := got.push (← byte s (r + 24 + k.toUInt64))
    if got.toList != a.toUTF8.toList then throw s!"toUTF8 {repr a}"
    let (h, _) ← call "lean_string_hash" [x] s
    if h != hash a then throw s!"hash {repr a}: {h}, where Lean gives {hash a}"

def numbers : Check := do
  for n in [0, 7, 9, 10, 99, 100, 12345, 2 ^ 32, 2 ^ 64 - 1] do
    let (r, s) ← call "lean_string_of_usize" [n.toUInt64] {}
    expect s!"of_usize {n}" (← take r s) (toString n)

def comparisons : Check := do
  for a in samples do for b in samples do
    let (x, s) := place a 1 0 {}
    let (y, s) := place b 1 0 s
    let (lt, _) ← call "lean_string_lt" [x, y] s
    if (lt == 1) != decide (a < b) then throw s!"{repr a} < {repr b}: {lt}"
    if a.utf8ByteSize == b.utf8ByteSize then
      let (eq, _) ← call "lean_string_eq_cold" [x, y] s
      if (eq == 1) != (a == b) then throw s!"{repr a} == {repr b}: {eq}"
    let n := min a.utf8ByteSize b.utf8ByteSize
    for l in [0:n + 1] do
      for len in [0:n + 1 - l] do
        let (same, _) ← call "lean_string_memcmp" [x, y, box l, box l, box len] s
        let wanted := (a.toUTF8.extract l (l + len)).toList == (b.toUTF8.extract l (l + len)).toList
        if (same == 1) != wanted then throw s!"memcmp {repr a} {repr b} {l} {len}"

def fromC : Check := do
  for a in samples do
    let bytes := a.toUTF8
    let (p, s0) := allocate (bytes.size + 1).toUInt64 {}
    let mut s := s0
    for i in [0:bytes.size] do s := setByte s (p + i.toUInt64) bytes[i]!
    s := setByte s (p + bytes.size.toUInt64) 0
    let (r, after) ← call "lean_mk_string" [p] s
    expect s!"mk_string {repr a}" (← take r after) a
  -- Bytes that are not UTF-8 stop the machine.
  for bad in [[0xFF], [0xC3], [0xE4, 0xB8], [0xED, 0xA0, 0x80], [0xC0, 0x80], [0x61, 0xF4, 0x90, 0x80, 0x80]] do
    let (p, s0) := allocate (bad.length + 1).toUInt64 {}
    let mut s := s0
    for (b, i) in bad.zipIdx do s := setByte s (p + i.toUInt64) b.toUInt8
    s := setByte s (p + bad.length.toUInt64) 0
    match Str.program.call outside 1000000 "lean_mk_string" [p] s with
    | .ok (.stopped _, _) => pure ()
    | _ => throw s!"mk_string of {bad} did not stop"

def checks : List (String × Check) := [
  ("appending, in place and copied, a string held once or twice", appends),
  ("pushing a character of each width", pushes),
  ("the character at, and the position after, every byte position and past the end", positions),
  ("every substring by byte positions, including ones not on a character", extracts),
  ("to a list of characters and back", lists),
  ("to bytes, and the hash", bytesOut),
  ("numbers in decimal", numbers),
  ("order, equality and comparing bytes, for every pair", comparisons),
  ("from C strings, and refusing bytes that are not UTF-8", fromC)]

end StringTest
