import Rv64Verifier.Proofs.Walk.R21KP
import Rv64Verifier.Proofs.Walk.OpenA

/-!
# `walk` R21: what it assumes of its callees and its front

* `ExtendSpecE` (an assumption, to be proved of `Pcs.ExtendSpec`'s function): `ExtendPre` asks
  `Src` of a claim's point only when it is nonempty (an empty point's pointer is unconstrained),
  and `ExtendPost` also says the claims `vec![ringswitch]` held are moved word for word, and every
  new claim's point lies in the heap (`HeapBuf`), as `verify_stacked_opening`'s `WeightSrc` wants.
* `OpenBridge OI OA`: the openings `walk`'s `OI` places in memory at its entry, in place there
  (`OpenPre`), give what `verify_stacked_opening`'s `OA` asks at its call (`Final.openBridge`).
* `LayoutWithin`: every placement fits the stack (`buildLayoutRust_within`).

`PlApart`, the placements' buffer missing the bus claims' buffer, is in `AtR17.lean`; the front
gives it.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript
  Rv64Verifier.PcsContracts Rv64Verifier.Pcs

/-- `n` bytes from `p`, aligned, below `NEXT` at `v`, in the heap unless empty. -/
@[rv_addr] def HeapBuf (v : MachineState) (p : Word) (n : Nat) : Prop :=
  p.toNat % 8 = 0 ∧ p.toNat + n ≤ heapNext v ∧ (n = 0 ∨ heapStart ≤ p.toNat)

/-- The buffers of the `RingWeight` at `a` lie in the heap. -/
def RingIn (v : MachineState) (a : Word) : Prop :=
  HeapBuf v (vecPtr v a) (24 * (vecLen v a).toNat) ∧
    HeapBuf v (vecPtr v (a + 24)) (24 * (vecLen v (a + 24)).toNat)

/-- The buffers of the `StackWeight` at `a` lie in the heap. -/
def WeightIn (v : MachineState) (a : Word) : Prop :=
  if v.getMem a = eqTag then HeapBuf v (vecPtr v (a + 8)) (24 * (vecLen v (a + 8)).toNat)
  else if v.getMem a = ringTag then RingIn v (a + 8)
  else RingIn v a

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

/-- `OI` at `walk`'s entry gives `OA` at `verify_stacked_opening`'s call (`a0` the transcript,
`a1` the root), memory changed only as `walk` may (`Inv`). -/
def OpenBridge (OI : MachineState → Word → List (List Opening) → Prop)
    (OA : MachineState → Word → TState → Prop) : Prop :=
  ∀ s v (T : TState), WalkPre s → OpenPre s → Inv s v → v.getMem (tp s) = s.getReg .x13 →
    v.getReg .x10 = tp s → v.getReg .x11 = s.getReg .x2 - 1800 →
    OI s (s.getReg .x13) T.proof.openings → OA v (tp s) T

/-- Every placement fits the stack. -/
def LayoutWithin (layout : LayoutMirror.LayoutRust) : Prop :=
  ∀ p ∈ layout.placements, ∀ q, p = some q → q.variableCount ≤ layout.stackLog

/-! ## The claims `extend` appends -/

/-- A claim as `columnClaimAt` reads it. -/
def toRustClaim (c : ColumnClaim) : LayoutMirror.ColumnClaimRust := ⟨c.column, c.point, c.value⟩

theorem columnClaimsAt_eq (u : MachineState) (P : Word) (L : Nat) :
    columnClaimsAt u P L = (claimsIn u P L).map toRustClaim := by
  simp only [columnClaimsAt, claimsIn, List.map_map]
  rfl

theorem filterMap_onStack (layout : LayoutMirror.LayoutRust) (cl : List ColumnClaim) :
    (cl.map toRustClaim).filterMap (onStackAt layout.placements layout.stackLog) =
      cl.filterMap (onStackRust layout) := by
  rw [List.filterMap_map]
  congr 1
  funext c
  simp only [Function.comp, onStackAt_eq, onStackRust, toRustClaim]

end Rv64Verifier.Proofs.Walk
