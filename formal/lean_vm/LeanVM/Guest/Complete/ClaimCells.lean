/-
  LeanVM.Guest.Complete.ClaimCells

  The claims' cells `main`'s buffers hold, on every node with `NodeRelation` and `ChildrenOk`.
-/

module

public import LeanVM.Guest.Complete.MainHypAt
public import LeanVM.Guest.Complete.Agg.Batched
public import LeanVM.Guest.Batch.Split
public import LeanVM.Guest.Batch.Node
public import LeanVM.Protocol.Verifier.Defers
public import LeanVM.Protocol.WithHashBridge

/-!
# The claims' cells

`fresh_shape_of_verifyDeferred`: a fresh claim the deferring verifier accepts has the program's
instruction coordinates (the link's index point cut at `log_bytecode`, which it is at least) and one
value per split column. `claimCells_of`: on the guest's bytecode, `55` cells per child's fresh
claim, `26` per child's deferred claim (`HasBytecodeShape`) and the node's own
(`DeferredClaimBatched`). `mainWinHypFromCallees_of_hyp`: `MainWinHypFromCallees` from
`MainHypFromCallees` alone.
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Verifier.Defers LeanVM.Node

@[expose] public section

/-- **An accepted fresh claim's shape**, from a run of the deferring verifier's program. -/
theorem fresh_shape_of_run (H : Bytes → Id Digest) (F : KeccakState → Id KeccakState)
    {bytecode : List K} {publicInput : Digest} {fresh : FreshClaim} {seed : KeccakState}
    {proof : Proof}
    (h : runProofWithHash (m := Id) H F (deferringVerifierProgram fresh bytecode publicInput) seed proof = true) :
    fresh.point.length = instructionVariableCount bytecode ∧
      fresh.values.length = (splitColumns tables).length := by
  unfold runProofWithHash at h
  revert h
  match hr : runWithHash (m := Id) H F (deferringVerifierProgram fresh bytecode publicInput)
      ⟨⟨seed, [], none⟩, proof.stream, proof.openings, []⟩ with
  | some (true, s) =>
    intro _
    have hR := VerifierProgram.returns_of_run H F hr
    rw [deferringVerifierProgram_eq, verifyExecution_split] at hR
    obtain ⟨u, hu, -⟩ := VerifierProgram.returns_bind hR
    obtain ⟨z, hz, hs⟩ := VerifierProgram.returns_bind hu
    obtain ⟨-, -, hl, -, hr'⟩ := execPre_facts hz
    have hs' := hs
    rw [freshSplit_bind] at hs'
    split at hs'
    · next hc =>
      refine ⟨?_, hc.2⟩
      rw [← hc.1, List.length_take, instructionVariableCount, hl, Nat.log2_two_pow]
      omega
    · cases hs'
  | some (false, _) => intro h; simp at h
  | none => intro h; simp at h

/-- **An accepted fresh claim's shape**: the program's instruction coordinates, one value per split
column. -/
theorem fresh_shape_of_verifyDeferred {bytecode : List K} {iv publicInput : Digest}
    {fresh : FreshClaim} {proof : Proof} (h : verifyDeferred bytecode iv publicInput fresh proof = true) :
    fresh.point.length = instructionVariableCount bytecode ∧
      fresh.values.length = (splitColumns tables).length := by
  rw [verifyDeferred_eq_withHash] at h
  exact fresh_shape_of_run _ _ h

/-- The guest's instructions have `19` coordinates. -/
theorem guest_instructionVariableCount : instructionVariableCount guestBytecode = 19 := by
  have h := Agg.guest_deferredVariableCount
  rw [deferredVariableCount, splitLog] at h
  omega

/-- A deferred claim of the guest's shape has `26` cells. -/
theorem deferred_cells_length {c : DeferredBytecodeClaim} (h : c.HasBytecodeShape guestBytecode) :
    c.cells.length = 26 := by
  rw [DeferredBytecodeClaim.HasBytecodeShape, Agg.guest_deferredVariableCount] at h
  simp [DeferredBytecodeClaim.cells, h]

/-- **The claims' cells**, on every node with `NodeRelation` and `ChildrenOk`. -/
theorem claimCells_of {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation guestBytecode guestSeed s w) (hok : ChildrenOk guestBytecode guestSeed w) :
    ClaimCells s w where
  fresh ch hch := by
    obtain ⟨hp, hv⟩ := fresh_shape_of_verifyDeferred (hok ch hch).verifies
    rw [guest_instructionVariableCount] at hp
    rw [Batch.length_splitColumns] at hv
    simp [FreshClaim.cells, hp, hv]
  carried ch hch := deferred_cells_length (hok ch hch).deferredClaimShaped
  own := deferred_cells_length (NodeRelation.hasBytecodeShape hr)

/-- **`MainWinHypFromCallees` from the windows at the honest oracle.** -/
theorem mainWinHypFromCallees_of_hyp {al : String → Bool} {k : ℕ} (h : MainHypFromCallees al k) :
    MainWinHypFromCallees al k :=
  mainWinHypFromCallees_of_at (fun _ _ hr hok => claimCells_of hr hok) h

end
end LeanVM.Guest.Complete
