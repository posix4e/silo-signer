import Mini.Run
import Mini.Alloc

/-! Sets the allocator as its language defines it against the allocator as printed and compiled.

    mini-fuzz <alloc-harness> <rounds> <requests a round> <seed>

Each round starts the compiled allocator on a small heap of its own, learns where that heap is, and gives the
same heap to the program run in Lean. Then it makes up requests: blocks of every size, frees, words written
into blocks that are in use and read back, and now and then a block freed twice. After each, both have to
say the same thing: the same address, the same word, the same reason for stopping. The proofs are about the
program as its language defines it; this is what holds the printer and the C compiler to it. -/

open Mini

/-- A word of memory, taking a byte nothing has written to be zero, as a fresh heap is. -/
def wordAt (memory : UInt64 → Option UInt8) (address : UInt64) : UInt64 := Id.run do
  let mut word : UInt64 := 0
  for i in [0:8] do
    word := word ||| (((memory (address + i.toUInt64)).getD 0).toUInt64 <<< (8 * i.toUInt64))
  return word

structure Round where
  state : State
  /-- Blocks in use: where each is and how many bytes were asked for. -/
  live : Array (UInt64 × UInt64) := #[]
  /-- A block just freed that the next request frees again. -/
  again : Option UInt64 := none
  seed : UInt64

def Round.next (r : Round) : UInt64 × Round :=
  let seed := r.seed * 6364136223846793005 + 1442695040888963407
  (seed >>> 33, { r with seed })

/-- What the program run in Lean says to a request, as the line the compiled one should print. -/
def answer (base heapSize : UInt64) (function : String) (argument : UInt64) (s : State) : String × Option State :=
  let outside : Outside := fun c _ s =>
    if c.startsWith "silo_plat_heap" then pure (base, { s with globals := put s.globals "heap_size" heapSize })
    else throw "oom"
  match Alloc.program.call outside 200000 function [argument] s with
  | .ok (.gave value, s) => (toString value, some s)
  | .ok (.on, s) => ("0", some s)
  | .ok (.stopped why, _) => (s!"stop {why}", none)
  | .error why => (why, none)

def main (arguments : List String) : IO UInt32 := do
  let [harness, rounds, requests, seed] := arguments
    | IO.eprintln "usage: mini-fuzz <alloc-harness> <rounds> <requests a round> <seed>"; return 2
  let heapSize : UInt64 := 32768
  -- With MINI_FUZZ_TRACE set, every request and both answers are written out as they happen.
  let trace := (← IO.getEnv "MINI_FUZZ_TRACE").isSome
  let mut seed := seed.toNat!.toUInt64
  let mut asked := 0
  for round in [0:rounds.toNat!] do
    let child ← IO.Process.spawn
      { cmd := harness, args := #[toString heapSize], stdin := .piped, stdout := .piped }
    let base := (← child.stdout.getLine).trimAscii.toString.toNat!.toUInt64
    let mut r : Round := { state := Alloc.program.start, seed := seed + round.toUInt64 * 7919 }
    let mut ended := false
    for _ in [0:requests.toNat!] do
      if ended then break
      let (choice, r1) := r.next
      let (pick, r2) := r1.next
      let (value, r3) := r2.next
      r := r3
      -- What to ask, and what the program run in Lean says to it.
      let mut line := ""
      let mut expected := ""
      if let some address := r.again then
        -- Freed twice in a row, with nothing in between: anything later could have been handed the block, and
        -- then freeing it again or writing into it would break the allocator's contract, not test it.
        let (said, after) := answer base heapSize "rt_free" address r.state
        line := s!"f {address} 0"; expected := said
        match after with
        | some s => r := { r with state := s, again := none }
        | none => ended := true
      else if choice % 10 < 4 || r.live.isEmpty then
        let size := if pick % 9 == 0 then pick % 9000 else pick % 300
        let (said, after) := answer base heapSize "rt_malloc" size r.state
        line := s!"m {size} 0"; expected := said
        match after with
        | some s => r := { r with state := s, live := r.live.push (said.toNat!.toUInt64, if size == 0 then 1 else size) }
        | none => ended := true
      else
        let index := (pick % r.live.size.toUInt64).toNat
        let (address, size) := r.live[index]!
        let at_ := address + (value % ((size + 7) / 8)) * 8
        if choice % 10 < 6 then
          let (said, after) := answer base heapSize "rt_free" address r.state
          line := s!"f {address} 0"; expected := said
          match after with
          -- One time in sixty-four the block is freed again straight away.
          | some s => r := { r with state := s, live := r.live.eraseIdx! index,
                                    again := if value % 64 == 0 then some address else none }
          | none => ended := true
        else if choice % 10 < 8 then
          line := s!"w {at_} {value}"; expected := "0"
          r := { r with state := { r.state with memory := writeBytes r.state.memory at_ value 8 } }
        else
          line := s!"r {at_} 0"; expected := toString (wordAt r.state.memory at_)
      if trace then IO.eprintln s!"{line}    expecting {expected}"
      child.stdin.putStrLn line
      child.stdin.flush
      let said := (← child.stdout.getLine).trimAscii.toString
      asked := asked + 1
      if said != expected then
        IO.println s!"FAIL  round {round} (seed {seed}): asked `{line}`"
        IO.println s!"      as its language defines it: {expected}"
        IO.println s!"      as printed and compiled:    {said}"
        return 1
    -- A round the allocator did not end has to be ended: the compiled one is waiting for the next request.
    if !ended then
      child.stdin.putStrLn "q 0 0"
      child.stdin.flush
    let _ ← child.wait
  IO.println s!"mini-fuzz: {rounds} rounds, {asked} requests, the two agreed on every one"
  return 0
