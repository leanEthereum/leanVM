/-
  LeanVM.Guest.HonestChildren

  Children carrying honest proofs are children the guest program accepts, and a child the deployed
  verifier accepts has a true fresh claim.
-/

module

public import LeanVM.Guest.Budget.Fits
public import LeanVM.Prover.EndChild
public import LeanVM.Protocol.Verifier.Defers

@[expose] public section

/-!
# Completeness on honest children

A child carrying an honest proof (`HonestChild`) is one the guest program accepts
(`AcceptableChild`) under the deployed seed: `NodeRelation`'s `ChildrenProven` gives its deferred
claim's shape and the deferring verifier's acceptance with its fresh claim, and
`guest_child_complete` the rest (`acceptableChildren_of_honest`). `EndExecFinal.lean` uses it to
run the guest program on honest children.

A child whose proof the deployed verifier accepts has a true fresh claim
(`freshClaim_holds_of_leanVmVerifier`): the deferring verifier accepts the proof with exactly one
claim, a true one (`verifyDeferred_of_leanVmVerifier`), and on a node `NodeRelation` admits under
the deployed seed, `ChildrenProven` has it accept the proof with the fresh claim.
-/

namespace LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakHash LeanVM.Node LeanVM.Guest

/-- `NodeRelation`'s third condition: every child is proven. -/
theorem childrenProven_of_nodeRelation {bytecode : List K} {seed : Digest}
    {statement : NodeStatement} {witness : NodeWitness}
    (h : NodeRelation bytecode seed statement witness) : ChildrenProven bytecode seed witness := by
  unfold NodeRelation at h
  exact h.2.2.1

/-- Children carrying honest proofs are children the guest program accepts, under the deployed
seed. -/
theorem acceptableChildren_of_honest {statement : NodeStatement} {witness : NodeWitness}
    (hRelation : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement
      witness)
    (hHonest : ∀ child ∈ witness.children, HonestChild child) :
    ∀ child ∈ witness.children,
      AcceptableChild (bytecodeWords guestProgram) (deployedSeed guestProgram) child :=
  fun child hc ↦
    let ⟨hShape, hVerifies⟩ := childrenProven_of_nodeRelation hRelation child hc
    Budget.guest_child_complete child (hHonest child hc) hShape hVerifies

/-- **A child the deployed verifier accepts has a true fresh claim**, on a node `NodeRelation`
admits under the deployed seed. -/
theorem freshClaim_holds_of_leanVmVerifier {statement : NodeStatement} {witness : NodeWitness}
    (hRelation : NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement
      witness)
    {child : Child} (hc : child ∈ witness.children)
    (hAccept : leanVmVerifier (m := Id) keccakF1600 guestProgram
      (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) child.statement))
        child.proof = true) :
    child.freshClaim.Holds (bytecodeWords guestProgram) := by
  obtain ⟨c, hHolds, -, hUnique⟩ := verifyDeferred_of_leanVmVerifier hAccept
  rw [End.publicDigest_publicInputOf] at hUnique
  rw [hUnique _ (childrenProven_of_nodeRelation hRelation child hc).2]
  exact hHolds

end LeanVM.Guest.Completeness

end
