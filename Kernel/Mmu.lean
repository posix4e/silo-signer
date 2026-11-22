/-! # Verified AArch64 Stage-1 MMU Descriptor & Memory Map Planner (`Kernel.Mmu`)

Formalizes the exact AArch64 VMSAv8-64 Stage-1 4 KiB / 2 MiB translation table descriptors and
identity-mapped physical region plan enforced by `boot/aarch64/early.c`:

- `MAIR_EL1`:
  - Index 0 (`0x00`): `Device-nGnRnE` (strictly ordered MMIO registers)
  - Index 1 (`0x44`): `Normal, Inner/Outer Non-Cacheable` (framebuffer / uncached DMA)
  - Index 2 (`0xFF`): `Normal, Inner/Outer Write-Back RW-Allocate` (kernel RAM)
- Strict `W^X`: no mapped page is ever both writable and executable; EL0 execution (`UXN`) is
  disabled everywhere; null page (`0x0`) and the stack guard hole are explicitly unmapped.

All safety properties are formally proved in `Kernel/MmuProofs.lean`. -/

namespace Kernel.Mmu

/-- Memory permission & attribute classes for bare-metal EL1 mappings. -/
inductive PagePerm where
  | unmapped    -- Fault on any access (null page, stack guard hole, holes)
  | codeRx      -- Normal-WB, EL1 Read-Only, EL1 Execute, UXN=1
  | roData      -- Normal-WB, EL1 Read-Only, PXN=1, UXN=1
  | rwData      -- Normal-WB, EL1 Read-Write, PXN=1, UXN=1
  | framebuffer -- Normal-NC, EL1 Read-Write, PXN=1, UXN=1
  | deviceMmio  -- Device-nGnRnE, EL1 Read-Write, PXN=1, UXN=1
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Translation granule level for a leaf entry. -/
inductive Granule where
  | page4K  -- L3 page descriptor (bits [1:0] = 0b11)
  | block2M -- L2 block descriptor (bits [1:0] = 0b01)
  deriving BEq, DecidableEq, Repr, Inhabited

/-- Exact `MAIR_EL1` value: Attr0=0x00 (Device-nGnRnE), Attr1=0x44 (Normal-NC), Attr2=0xFF (Normal-WB). -/
def mairValue : UInt64 := 0x0000000000FF4400

def bitValid : UInt64 := 1
def bitTableOrPage : UInt64 := 2
def bitAF : UInt64 := (1 : UInt64) <<< 10
def shOuter : UInt64 := (2 : UInt64) <<< 8
def shInner : UInt64 := (3 : UInt64) <<< 8
def apEl1Rw : UInt64 := (0 : UInt64) <<< 6
def apEl1Ro : UInt64 := (2 : UInt64) <<< 6
def bitPXN : UInt64 := (1 : UInt64) <<< 53
def bitUXN : UInt64 := (1 : UInt64) <<< 54

def attrDevice : UInt64 := (0 : UInt64) <<< 2
def attrNormalNc : UInt64 := (1 : UInt64) <<< 2
def attrNormalWb : UInt64 := (2 : UInt64) <<< 2

/-- Output address mask: bits `[47:12]` for 4 KiB pages, `[47:21]` for 2 MiB blocks. -/
def addrMask : Granule → UInt64
  | .page4K  => 0x0000FFFFFFFFF000
  | .block2M => 0x0000FFFFFFE00000

def leafTypeBits : Granule → UInt64
  | .page4K  => bitValid ||| bitTableOrPage -- 0b11
  | .block2M => bitValid                    -- 0b01

/-- Encodes a complete 64-bit AArch64 Stage-1 leaf translation descriptor. -/
def encodeDescriptor (perm : PagePerm) (g : Granule) (pa : UInt64) : UInt64 :=
  let addr := pa &&& addrMask g
  let ty := leafTypeBits g
  match perm with
  | .unmapped    => 0
  | .codeRx      => addr ||| ty ||| attrNormalWb ||| apEl1Ro ||| shInner ||| bitAF ||| bitUXN
  | .roData      => addr ||| ty ||| attrNormalWb ||| apEl1Ro ||| shInner ||| bitAF ||| bitPXN ||| bitUXN
  | .rwData      => addr ||| ty ||| attrNormalWb ||| apEl1Rw ||| shInner ||| bitAF ||| bitPXN ||| bitUXN
  | .framebuffer => addr ||| ty ||| attrNormalNc ||| apEl1Rw ||| shOuter ||| bitAF ||| bitPXN ||| bitUXN
  | .deviceMmio  => addr ||| ty ||| attrDevice   ||| apEl1Rw |||            bitAF ||| bitPXN ||| bitUXN

/-- Hardware bit predicates directly matching the ARMv8/v9 VMSAv8-64 Stage-1 format. -/
def isValid (d : UInt64) : Bool := (d &&& 1) == 1
def isWritable (d : UInt64) : Bool := isValid d && ((d >>> 6) &&& 3) == 0
def isExecEl1 (d : UInt64) : Bool := isValid d && ((d >>> 53) &&& 1) == 0
def isExecEl0 (d : UInt64) : Bool := isValid d && ((d >>> 54) &&& 1) == 0
def attrIndex (d : UInt64) : UInt64 := (d >>> 2) &&& 7

/-- One contiguous physical/identity-mapped memory region `[base, base + size)`. -/
structure Region where
  base : Nat
  size : Nat
  perm : PagePerm
  deriving BEq, DecidableEq, Repr, Inhabited

def Region.contains (r : Region) (addr : Nat) : Bool :=
  r.base ≤ addr && addr < r.base + r.size

def Region.aligned4K (r : Region) : Bool :=
  r.base % 4096 == 0 && r.size % 4096 == 0 && r.size > 0

def Region.disjoint (a b : Region) : Bool :=
  a.base + a.size ≤ b.base || b.base + b.size ≤ a.base

/-- Complete identity-mapped memory plan for a bare-metal Tricorder image. -/
structure MemoryPlan where
  stackGuardAddr : Nat
  regions : List Region
  deriving BEq, Repr, Inhabited

/-- Looks up the effective permission at `addr` (first matching region, or `.unmapped`). -/
def lookupPerm (regions : List Region) (addr : Nat) : PagePerm :=
  match regions with
  | [] => .unmapped
  | r :: rs => if r.contains addr then r.perm else lookupPerm rs addr

def allPairwiseDisjoint : List Region → Bool
  | [] => true
  | r :: rs => rs.all (Region.disjoint r) && allPairwiseDisjoint rs

/-- Executable validator checked at boot & in proofs:
- Every region is 4 KiB-aligned, non-empty, and pairwise disjoint;
- Null page (`0x0`) is unmapped;
- Stack guard page (`stackGuardAddr`) is unmapped. -/
def validatePlan (p : MemoryPlan) : Bool :=
  p.regions.all Region.aligned4K &&
  allPairwiseDisjoint p.regions &&
  p.stackGuardAddr % 4096 == 0 &&
  lookupPerm p.regions 0 == .unmapped &&
  lookupPerm p.regions p.stackGuardAddr == .unmapped

/-- Builds the canonical Tricorder bare-metal memory plan from linker & boot symbols. -/
def buildCanonicalPlan
    (textBase textSize roBase roSize stackGuardBase stackBase stackSize
     dataBase dataSize heapBase heapSize dmaBase dmaSize : Nat)
    (fb? : Option (Nat × Nat))
    (mmioWindows : List (Nat × Nat)) : MemoryPlan :=
  let baseRegs : List Region := [
    { base := textBase, size := textSize, perm := .codeRx },
    { base := roBase,   size := roSize,   perm := .roData },
    { base := stackBase, size := stackSize, perm := .rwData },
    { base := dataBase, size := dataSize, perm := .rwData },
    { base := heapBase, size := heapSize, perm := .rwData },
    { base := dmaBase,  size := dmaSize,  perm := .rwData }
  ]
  let withFb := match fb? with
    | some (b, s) => baseRegs ++ [{ base := b, size := s, perm := .framebuffer }]
    | none => baseRegs
  let withMmio := withFb ++ mmioWindows.map fun (b, s) => { base := b, size := s, perm := .deviceMmio }
  { stackGuardAddr := stackGuardBase, regions := withMmio }

end Kernel.Mmu
