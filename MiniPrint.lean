import Mini.Print
import Mini.Alloc
import Mini.Free
import Mini.Number
import Mini.Array
import Mini.Small
import Mini.Hash
import Mini.String
import Mini.Secret

/-! Prints the C that the programs in `Mini/` stand for (`scripts/print-runtime`). -/

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["alloc"] => IO.print (Mini.Alloc.program.c "Mini/Alloc.lean"); return 0
  | ["free"] => IO.print (Mini.Free.program.c "Mini/Free.lean"); return 0
  | ["number"] => IO.print (Mini.Number.program.c "Mini/Number.lean"); return 0
  | ["array"] => IO.print (Mini.Array.program.c "Mini/Array.lean"); return 0
  | ["small"] => IO.print (Mini.Small.program.c "Mini/Small.lean"); return 0
  | ["hash"] => IO.print (Mini.Hash.program.c "Mini/Hash.lean"); return 0
  | ["string"] => IO.print (Mini.Str.program.c "Mini/String.lean"); return 0
  | ["secret"] => IO.print (Mini.Secret.program.c "Mini/Secret.lean"); return 0
  | _ => IO.eprintln "usage: mini-print alloc | free | number | array | small | hash | string | secret"; return 2
