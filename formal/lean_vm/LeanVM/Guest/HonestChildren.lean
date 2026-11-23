/-
  LeanVM.Guest.HonestChildren

  Children carrying honest proofs are children the guest program accepts.
-/

module

public import LeanVM.Guest.Budget.Fits
public import LeanVM.Prover.EndChild

@[expose] public section

/-!
# Completeness on honest children

A child carrying an honest proof (`HonestChild`) is one the guest program accepts
(`AcceptableChild`) under the deployed seed: `NodeRelation`'s `ChildrenProven` gives its deferred
claim's shape and the deferring verifier's acceptance with its fresh claim, and
`guest_child_complete` the rest (`acceptableChildren_of_honest`). `EndExecHonest.lean` uses it to
run the guest program on honest children.
-/

namespace LeanVM.Guest.Completeness

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Node LeanVM.Guest

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

end LeanVM.Guest.Completeness

end
