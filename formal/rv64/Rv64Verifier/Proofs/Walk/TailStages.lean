import Rv64Verifier.Proofs.Walk.TailModel

/-!
# `walk`'s mirror after the table phase, stage by stage

`afterTables` is the public input's claims, then `afterPublic`; that is `verify_keccak`'s phase,
then `afterKeccak`; that is `ring_switch`, then `afterRing`: `verify_stacked_opening`, then
`finish` on the summary. Each a bind for `TracksR.bind`.
-/

namespace Rv64Verifier.Proofs.Walk
open RiscvZkvm.Rv64 LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
  LeanVM.Protocol.Verifier Rv64Verifier.Runtime Rv64Verifier.Model Rv64Verifier.Transcript

/-- The summary `walk` returns. -/
def summaryOf (layout : LayoutMirror.LayoutRust) (tableRows : List (BitVec 64))
    (logInverseRate : BitVec 64) (bus : BusResultRust) (keccakStart keccakEnd : ℕ) : SummaryRust :=
  ⟨layout.logMemory, tableRows, logInverseRate.toNat, bus.bytecodePoint, (keccakStart, keccakEnd)⟩

/-- From `ring_switch`'s result on. -/
def afterRing (layout : LayoutMirror.LayoutRust) (tableRows : List (BitVec 64))
    (logInverseRate : BitVec 64) (bus : BusResultRust) (claims : List ColumnClaim)
    (keccakStart keccakEnd : ℕ) (ring : E × Pcs.RingWeightRust) : TM SummaryRust :=
  Pcs.verifyStackedOpeningRust layout.stackLog logInverseRate.toNat
      (⟨.placedRing layout.qkeccak ring.2, ring.1⟩ :: claims.filterMap (onStackRust layout)) >>=
    fun _ ↦ finishRust (summaryOf layout tableRows logInverseRate bus keccakStart keccakEnd)

/-- From `verify_keccak`'s phase's result on. -/
def afterKeccak (layout : LayoutMirror.LayoutRust) (tableRows : List (BitVec 64))
    (logInverseRate : BitVec 64) (bus : BusResultRust) (claims : List ColumnClaim)
    (r : Gkr.KeccakOpenings × ℕ × ℕ) : TM SummaryRust :=
  Pcs.ringSwitchRust r.1.inputs.1 r.1.inputs.2 >>=
    afterRing layout tableRows logInverseRate bus (claims ++
      r.1.outputs.toList.map fun pw ↦ (⟨LayoutMirror.qkeccakRust, pw.1, pw.2⟩ : ColumnClaim))
      r.2.1 r.2.2

/-- From the public input's claims on. -/
def afterPublic (layout : LayoutMirror.LayoutRust) (tableRows : List (BitVec 64))
    (logInverseRate : BitVec 64) (bus : BusResultRust) (evaluations : List (List E × List E))
    (claims : List ColumnClaim) (publicClaims : List ColumnClaim) : TM SummaryRust :=
  keccakPhaseRust layout evaluations >>=
    afterKeccak layout tableRows logInverseRate bus (claims ++ publicClaims)

theorem afterTables_stages (publicInput : List (BitVec 8)) (layout : LayoutMirror.LayoutRust)
    (tableRows : List (BitVec 64)) (lir : BitVec 64) (bus : BusResultRust)
    (evaluations : List (List E × List E)) :
    afterTables publicInput layout tableRows lir bus evaluations =
      publicInputRust layout publicInput >>= afterPublic layout tableRows lir bus evaluations
        (bus.claims ++ tableClaimsRust evaluations) := by
  simp only [afterTables, bind_assoc, pure_bind]
  rfl

end Rv64Verifier.Proofs.Walk
