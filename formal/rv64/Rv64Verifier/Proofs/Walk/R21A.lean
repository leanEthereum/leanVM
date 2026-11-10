import Rv64Verifier.Proofs.Walk.R21KP
import Rv64Verifier.Proofs.Walk.OpenA
import Rv64Verifier.Proofs.Pcs.ExtendContracts

/-!
# `walk` R21: what it assumes of its callees and its front

* `ExtendSpecE` (`Pcs/ExtendContracts.lean`, proved as `Pcs.extendE`): `extend_desugared`'s
  contract as R21 calls it.
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

/-- The buffers of the `RingWeight` at `a` lie in the heap. -/
def RingIn (v : MachineState) (a : Word) : Prop :=
  HeapBuf v (vecPtr v a) (24 * (vecLen v a).toNat) ∧
    HeapBuf v (vecPtr v (a + 24)) (24 * (vecLen v (a + 24)).toNat)

/-- The buffers of the `StackWeight` at `a` lie in the heap. -/
def WeightIn (v : MachineState) (a : Word) : Prop :=
  if v.getMem a = eqTag then HeapBuf v (vecPtr v (a + 8)) (24 * (vecLen v (a + 8)).toNat)
  else if v.getMem a = ringTag then RingIn v (a + 8)
  else RingIn v a

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
