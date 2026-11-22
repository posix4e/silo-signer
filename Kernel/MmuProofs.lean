import Kernel.Mmu

/-! # Formal Proofs for AArch64 Stage-1 MMU Safety (`Kernel.MmuProofs`)

Machine-checked proofs directly inside Lean's trusted kernel (zero `bv_decide`, zero
`native_decide`, standard axioms `[propext, Quot.sound, Classical.choice]` only) over the 64-bit
AArch64 VMSAv8-64 descriptor encoding:

1. **Strict `W^X`**: no encoded descriptor is ever both writable (`AP=RW`) and executable (`PXN=0 ∨ UXN=0`).
2. **EL0 Execute-Never**: every valid descriptor enforces `UXN = 1`.
3. **Device Non-Executable & Device-nGnRnE**: every MMIO descriptor has `AttrIndx = 0`, `PXN = 1`, `UXN = 1`.
4. **Unmapped Fault**: unmapped descriptors encode to `0` (`isValid = false`).
5. **Validated Plan Invariants**: any validated `MemoryPlan` leaves the null page (`0x0`) and stack guard
   page unmapped, and guarantees `W^X` at every physical address. -/

namespace Kernel.MmuProofs

open Kernel.Mmu

/-- Pure kernel bitfield isolation lemma: if `(mask >>> s) &&& m = 0`, then extracting `m` at shift `s`
from `(pa &&& mask) ||| flags` depends ONLY on `flags`, independent of `pa`. -/
private theorem extract_or_masked (pa mask flags s m : UInt64)
    (h : ((mask >>> s) &&& m) = 0) :
    ((((pa &&& mask) ||| flags) >>> s) &&& m) = ((flags >>> s) &&& m) := by
  apply UInt64.eq_of_toBitVec_eq
  have hb : (mask.toBitVec >>> (s.toNat % 64)) &&& m.toBitVec = 0#64 := by
    have := congrArg UInt64.toBitVec h
    simpa [UInt64.toBitVec_and, UInt64.toBitVec_shiftRight] using this
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or, UInt64.toBitVec_shiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hbi : mask.toBitVec.getLsbD (s.toNat % 64 + i) = true → m.toBitVec.getLsbD i = false := by
    have := congrArg (fun x => x.getLsbD i) hb
    simpa [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight] using this
  simp only [BitVec.getLsbD_and]
  cases hm : m.toBitVec.getLsbD i
  · simp
  · have hmf : mask.toBitVec.getLsbD (s.toNat % 64 + i) = false := by
      cases hmask : mask.toBitVec.getLsbD (s.toNat % 64 + i)
      · rfl
      · exfalso
        have := hbi hmask
        rw [hm] at this
        contradiction
    simp [hmf]

private theorem extract_or_masked0 (pa mask flags m : UInt64)
    (h : (mask &&& m) = 0) :
    (((pa &&& mask) ||| flags) &&& m) = (flags &&& m) := by
  apply UInt64.eq_of_toBitVec_eq
  have hb : mask.toBitVec &&& m.toBitVec = 0#64 := by
    have := congrArg UInt64.toBitVec h
    simpa [UInt64.toBitVec_and] using this
  simp only [UInt64.toBitVec_and, UInt64.toBitVec_or]
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hbi : mask.toBitVec.getLsbD i = true → m.toBitVec.getLsbD i = false := by
    have := congrArg (fun x => x.getLsbD i) hb
    simpa [BitVec.getLsbD_and] using this
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases hm : m.toBitVec.getLsbD i
  · simp
  · have hmf : mask.toBitVec.getLsbD i = false := by
      cases hmask : mask.toBitVec.getLsbD i
      · rfl
      · exfalso
        have := hbi hmask
        rw [hm] at this
        contradiction
    simp [hmf]

private theorem mask_bit0_zero (g : Granule) : (addrMask g &&& 1) = 0 := by
  cases g <;> decide
private theorem mask_ap_zero (g : Granule) : ((addrMask g >>> 6) &&& 3) = 0 := by
  cases g <;> decide
private theorem mask_pxn_zero (g : Granule) : ((addrMask g >>> 53) &&& 1) = 0 := by
  cases g <;> decide
private theorem mask_uxn_zero (g : Granule) : ((addrMask g >>> 54) &&& 1) = 0 := by
  cases g <;> decide
private theorem mask_attr_zero (g : Granule) : ((addrMask g >>> 2) &&& 7) = 0 := by
  cases g <;> decide

/-- Constant flags component of `encodeDescriptor` (independent of `pa`). -/
def permFlags (perm : PagePerm) (g : Granule) : UInt64 :=
  let ty := leafTypeBits g
  match perm with
  | .unmapped    => 0
  | .codeRx      => ty ||| attrNormalWb ||| apEl1Ro ||| shInner ||| bitAF ||| bitUXN
  | .roData      => ty ||| attrNormalWb ||| apEl1Ro ||| shInner ||| bitAF ||| bitPXN ||| bitUXN
  | .rwData      => ty ||| attrNormalWb ||| apEl1Rw ||| shInner ||| bitAF ||| bitPXN ||| bitUXN
  | .framebuffer => ty ||| attrNormalNc ||| apEl1Rw ||| shOuter ||| bitAF ||| bitPXN ||| bitUXN
  | .deviceMmio  => ty ||| attrDevice   ||| apEl1Rw |||            bitAF ||| bitPXN ||| bitUXN

private theorem encodeDescriptor_eq_or (perm : PagePerm) (g : Granule) (pa : UInt64)
    (hp : perm ≠ .unmapped) :
    encodeDescriptor perm g pa = (pa &&& addrMask g) ||| permFlags perm g := by
  cases perm
  · exact absurd rfl hp
  all_goals
    simp only [encodeDescriptor, permFlags, UInt64.or_assoc]

/-- **W^X Theorem**: No encoded AArch64 Stage-1 descriptor is ever simultaneously writable and executable. -/
theorem encodeDescriptor_wx (perm : PagePerm) (g : Granule) (pa : UInt64) :
    ¬ (isWritable (encodeDescriptor perm g pa) = true ∧
       (isExecEl1 (encodeDescriptor perm g pa) = true ∨ isExecEl0 (encodeDescriptor perm g pa) = true)) := by
  cases perm
  · simp [encodeDescriptor, isWritable, isValid]
  all_goals
    rw [encodeDescriptor_eq_or _ g pa (by decide)]
    simp only [isWritable, isExecEl1, isExecEl0, isValid,
      extract_or_masked0 pa (addrMask g) _ 1 (mask_bit0_zero g),
      extract_or_masked pa (addrMask g) _ 6 3 (mask_ap_zero g),
      extract_or_masked pa (addrMask g) _ 53 1 (mask_pxn_zero g),
      extract_or_masked pa (addrMask g) _ 54 1 (mask_uxn_zero g)]
    cases g <;> decide

/-- Every descriptor forbids EL0 execution (`UXN = 1` whenever valid). -/
theorem encodeDescriptor_no_el0_exec (perm : PagePerm) (g : Granule) (pa : UInt64) :
    isExecEl0 (encodeDescriptor perm g pa) = false := by
  cases perm
  · simp [encodeDescriptor, isExecEl0, isValid]
  all_goals
    rw [encodeDescriptor_eq_or _ g pa (by decide)]
    simp only [isExecEl0, isValid,
      extract_or_masked0 pa (addrMask g) _ 1 (mask_bit0_zero g),
      extract_or_masked pa (addrMask g) _ 54 1 (mask_uxn_zero g)]
    cases g <;> decide

/-- Every MMIO device descriptor has `Device-nGnRnE` (`AttrIndx = 0`) and is non-executable at EL1 and EL0. -/
theorem encodeDescriptor_device_safe (g : Granule) (pa : UInt64) :
    attrIndex (encodeDescriptor .deviceMmio g pa) = 0 ∧
    isExecEl1 (encodeDescriptor .deviceMmio g pa) = false ∧
    isExecEl0 (encodeDescriptor .deviceMmio g pa) = false := by
  rw [encodeDescriptor_eq_or .deviceMmio g pa (by decide)]
  simp only [attrIndex, isExecEl1, isExecEl0, isValid,
    extract_or_masked0 pa (addrMask g) _ 1 (mask_bit0_zero g),
    extract_or_masked pa (addrMask g) _ 2 7 (mask_attr_zero g),
    extract_or_masked pa (addrMask g) _ 53 1 (mask_pxn_zero g),
    extract_or_masked pa (addrMask g) _ 54 1 (mask_uxn_zero g)]
  cases g <;> decide

private theorem pagePerm_eq_of_beq {a b : PagePerm} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

/-- Unmapped entries are strictly invalid (bit 0 = 0), forcing a synchronous Translation Fault. -/
theorem encodeDescriptor_unmapped_invalid (g : Granule) (pa : UInt64) :
    isValid (encodeDescriptor .unmapped g pa) = false := by
  simp [encodeDescriptor, isValid]

/-- A validated `MemoryPlan` leaves the null page (`0x0`) unmapped. -/
theorem validatePlan_null_unmapped (p : MemoryPlan) (hv : validatePlan p = true) :
    lookupPerm p.regions 0 = .unmapped := by
  simp only [validatePlan, Bool.and_eq_true] at hv
  exact pagePerm_eq_of_beq hv.1.2

/-- A validated `MemoryPlan` leaves its stack guard page unmapped (overflow triggers Data Abort). -/
theorem validatePlan_stack_guard_unmapped (p : MemoryPlan) (hv : validatePlan p = true) :
    lookupPerm p.regions p.stackGuardAddr = .unmapped := by
  simp only [validatePlan, Bool.and_eq_true] at hv
  exact pagePerm_eq_of_beq hv.2

/-- At every address in any `MemoryPlan`, the generated Stage-1 descriptor satisfies `W^X`. -/
theorem plan_address_wx (p : MemoryPlan) (g : Granule) (addr : Nat) :
    let d := encodeDescriptor (lookupPerm p.regions addr) g (UInt64.ofNat addr)
    ¬ (isWritable d = true ∧ (isExecEl1 d = true ∨ isExecEl0 d = true)) := by
  intro d
  exact encodeDescriptor_wx (lookupPerm p.regions addr) g (UInt64.ofNat addr)

end Kernel.MmuProofs
