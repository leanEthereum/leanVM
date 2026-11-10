import Rv64Verifier.Proofs.Pcs.Contracts

/-!
# `extend_desugared`'s contract as `walk`'s R21 calls it

`ExtendSpecE`: `ExtendPre` asks `Src` of a claim's point only when it is nonempty (an empty
point's pointer is unconstrained), and `ExtendPost` also says the claims `vec![ringswitch]` held
are moved word for word, and every new claim's point lies in the heap (`HeapBuf`), as
`verify_stacked_opening`'s `WeightSrc` wants. In `walk`'s namespace, which states it; proved as
`Pcs.extendE`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 Rv64Verifier.Runtime Rv64Verifier.Transcript Rv64Verifier.PcsContracts
  Rv64Verifier.Pcs

/-- `n` bytes from `p`, aligned, below `NEXT` at `v`, in the heap unless empty. -/
@[rv_addr] def HeapBuf (v : MachineState) (p : Word) (n : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ p.toNat + n ≤ heapNext v ∧ (n = 0 ∨ heapStart ≤ p.toNat)

/-- `ExtendPre`, a claim's point read only when nonempty. -/
structure ExtendPreE (s : MachineState) : Prop where
  heap : HeapOk s
  stack : RtStack s extendStack
  rodata : RodataOk s
  self : Dst s extendStack (s.getReg .x10) 24
  vec : VecOk s (s.getReg .x10) 88 8
  iter : Dst s extendStack (s.getReg .x11) 24
  bounds : (itCur s).toNat ≤ (itEnd s).toNat ∧ ((itEnd s).toNat - (itCur s).toNat) % 56 = 0
  claims : Src s extendStack (itCur s) (56 * itCount s)
  points : ∀ i < itCount s, (vecLen s (itCur s + BitVec.ofNat 64 (56 * i))).toNat = 0 ∨
    Src s extendStack (vecPtr s (itCur s + BitVec.ofNat 64 (56 * i)))
      (24 * (vecLen s (itCur s + BitVec.ofNat 64 (56 * i))).toNat)
  layout : Src s extendStack (itLayout s) 192
  placements : Src s extendStack (placementsPtr s) (24 * placementsLen s)
  within : ∀ p ∈ placementsAt s (placementsPtr s) (placementsLen s), ∀ q, p = some q →
    q.variableCount ≤ stackLogAt s
  selfIter : Apart (s.getReg .x10) 24 (s.getReg .x11) 24
  full : vecLen s (s.getReg .x10) = vecCap s (s.getReg .x10)
  elems : Src s extendStack (vecPtr s (s.getReg .x10)) (88 * (vecLen s (s.getReg .x10)).toNat)
  weights : ∀ i < (vecLen s (s.getReg .x10)).toNat,
    WeightSrc s extendStack (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i))
  elemsOff : ExtendOff s (vecPtr s (s.getReg .x10)) (88 * (vecLen s (s.getReg .x10)).toNat)
  weightsOff : ∀ i < (vecLen s (s.getReg .x10)).toNat,
    WeightApart s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) (s.getReg .x10) 24 ∧
      WeightApart s (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i)) (s.getReg .x11) 24
  claimsOff : ExtendOff s (itCur s) (56 * itCount s)
  pointsOff : ∀ i < itCount s, ExtendOff s (vecPtr s (itCur s + BitVec.ofNat 64 (56 * i)))
    (24 * (vecLen s (itCur s + BitVec.ofNat 64 (56 * i))).toNat)
  layoutOff : ExtendOff s (itLayout s) 192
  placementsOff : ExtendOff s (placementsPtr s) (24 * placementsLen s)

/-- `ExtendPost`, the old claims moved word for word and the new claims' points in the heap. -/
structure ExtendPostE (s t : MachineState) : Prop extends ExtendPost s t where
  moved : ∀ i < (vecLen s (s.getReg .x10)).toNat, ∀ k < 11,
    t.getMem (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (88 * i + 8 * k)) =
      s.getMem (vecPtr s (s.getReg .x10) + BitVec.ofNat 64 (88 * i + 8 * k))
  added : ∀ i, (vecLen s (s.getReg .x10)).toNat ≤ i → i < (vecLen t (s.getReg .x10)).toNat →
    HeapBuf t (vecPtr t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (88 * i + 8)))
      (24 * (vecLen t (vecPtr t (s.getReg .x10) + BitVec.ofNat 64 (88 * i + 8))).toNat)

abbrev ExtendSpecE : Prop := FunSpec Image.code 0x80009b94 ExtendPreE ExtendPostE

end Rv64Verifier.Proofs.Walk
