/-
  LeanVM.Guest.HonestChildren

  Children carrying honest proofs are children the guest program accepts, and the honest proof
  rarely refused (`HonestProofRarelyRefused`), from the honest proof being such a child.
-/

module

public import LeanVM.Guest.Child.FreshUnique
public import LeanVM.Guest.Budget.Fits
public import LeanVM.Prover.EndChild

@[expose] public section

/-!
# Completeness on honest children

A child carrying an honest proof (`HonestChild`) is one the guest program accepts
(`AcceptableChild`) under the deployed seed: `guest_child_complete` gives some true claim with which
the honest proof is an acceptable child, and `NodeRelation`'s `ChildrenProven` has the deferring
verifier accept the proof with the witness's fresh claim, which is true; the deferring verifier
accepts a proof with at most one true claim (`Child.freshClaim_unique`), so the two claims are one
(`acceptableChild_of_honestChild`). `EndExecHonest.lean` uses it to run the guest program on
honest children.
-/

namespace LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest

/-- **A child carrying an honest proof is one the guest program accepts**, under the deployed seed,
wherever the deferring verifier accepts its proof with its fresh claim (`ChildrenProven`). -/
theorem acceptableChild_of_honestChild {witness : NodeWitness}
    (hProven : ChildrenProven (bytecodeWords guestProgram) (deployedSeed guestProgram) witness)
    {child : Child} (hc : child ∈ witness.children) (hHonest : HonestChild child) :
    AcceptableChild (bytecodeWords guestProgram) (deployedSeed guestProgram) child := by
  obtain ⟨hHolds, execution, ρ, hSome, hAccepted⟩ := hHonest
  obtain ⟨hShape, hVerifies⟩ := hProven child hc
  obtain ⟨fresh, hFresh, hOk⟩ := Budget.guest_child_complete.2 child.statement execution ρ
    hShape child.proof hSome hAccepted
  have hEq : fresh = child.freshClaim :=
    LeanVM.Guest.Child.freshClaim_unique hOk.verifies hVerifies hFresh hHolds
  obtain ⟨statement, freshClaim, proof⟩ := child
  subst hEq
  exact hOk

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
  fun child hc ↦ acceptableChild_of_honestChild (childrenProven_of_nodeRelation hRelation) hc
    (hHonest child hc)

/-- **The honest proof is rarely refused** (`HonestProofRarelyRefused`): `guest_child_complete`'s
first part. -/
theorem honest_proof_rarely_refused : HonestProofRarelyRefused :=
  Budget.guest_child_complete.1

end LeanVM.Guest.Completeness

end
