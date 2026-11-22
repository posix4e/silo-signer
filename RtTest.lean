import SelfTest
import Platform
import Secret

/-! # The self-test's transcript, printed

Linked once against Lean's own runtime (`rt-test`) and once against the minimal runtime (`rt-test-min`); the
two outputs must be byte for byte the same. -/

/-- Comparing and choosing without secrets deciding the time (`Secret.lean`). -/
def secrets : String := Id.run do
  let bytes (l : List Nat) := ByteArray.mk (l.map (·.toUInt8)).toArray
  let a := bytes [1, 2, 3, 4, 5, 6, 7, 8, 9]
  let mut lines := ""
  for (name, b) in [("same", bytes [1, 2, 3, 4, 5, 6, 7, 8, 9]), ("first differs", bytes [0, 2, 3, 4, 5, 6, 7, 8, 9]),
      ("last differs", bytes [1, 2, 3, 4, 5, 6, 7, 8, 8]), ("shorter", bytes [1, 2, 3]), ("empty", ByteArray.empty)] do
    lines := lines ++ s!"secret equal, {name}: {Secret.equal a b}\n"
  lines := lines ++ s!"secret equal, both empty: {Secret.equal ByteArray.empty ByteArray.empty}\n"
  lines := lines ++ s!"secret select: {Secret.select true 7 9} {Secret.select false 7 9} {Secret.select true 0xFFFFFFFFFFFFFFFF 0}\n"
  return lines

def main : IO UInt32 := do
  Platform.write (SelfTest.transcript ++ secrets.toUTF8)
  return 0
