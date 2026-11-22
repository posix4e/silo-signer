import Kernel.Rng

/-! # Formal Proofs for Hardware RNG Health Checks (`Kernel.RngProofs`)

Proves fail-closed rejection of degenerate hardware RNG outputs:
1. All-zero words are always rejected.
2. All-ones (`0xFFFFFFFFFFFFFFFF`) words are always rejected.
3. Any repeated/stuck 64-bit word is always rejected.
4. `conditionBlock` fails whenever `wordsHealthy` fails (never outputs bytes on bad entropy). -/

namespace Kernel.RngProofs

open Kernel.Rng

/-- An all-zero hardware RNG output is always rejected. -/
theorem wordsHealthy_rejects_zero : wordsHealthy 0 0 0 0 = false := by
  decide

/-- An all-`0xFF` hardware RNG output is always rejected. -/
theorem wordsHealthy_rejects_ones :
    wordsHealthy 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF 0xFFFFFFFFFFFFFFFF = false := by
  decide

/-- A stuck hardware RNG repeating the same 64-bit word is always rejected. -/
theorem wordsHealthy_rejects_constant (w : UInt64) :
    wordsHealthy w w w w = false := by
  simp [wordsHealthy]

/-- Any adjacent duplicate 64-bit word (`w0 = w1`) is rejected. -/
theorem wordsHealthy_rejects_adj_dup (w w2 w3 : UInt64) :
    wordsHealthy w w w2 w3 = false := by
  simp [wordsHealthy]

/-- `conditionBlock` fails closed whenever `wordsHealthy` is false. -/
theorem conditionBlock_fail_closed (w0 w1 w2 w3 ctr : UInt64)
    (h : wordsHealthy w0 w1 w2 w3 = false) :
    (conditionBlock w0 w1 w2 w3 ctr).isOk = false := by
  simp [conditionBlock, h, Except.isOk, Except.toBool]

end Kernel.RngProofs
