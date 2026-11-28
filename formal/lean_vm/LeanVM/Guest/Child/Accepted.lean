/-
  LeanVM.Guest.Child.Accepted

  A child the deferring verifier accepts, its openings agreeing in the caps, is one the guest
  program accepts; so the children of a node `NodeRelation` admits are, or a child's proof exhibits
  a Keccak-256 collision.
-/

module

public import LeanVM.Guest.Child.Collision
public import LeanVM.Guest.Child.StackLog
public import LeanVM.Guest.Limits

/-!
# Children the verifier accepts

`acceptableChild_of_accepted`: a child whose proof the deferring verifier accepts, with a deferred
claim of the bytecode's shape (`NodeRelation`'s `ChildrenProven`), is a child the guest program
accepts (`AcceptableChild`) wherever its openings agree at every query step of its verifier's run:

* its stack log is at least `minChildStackLog` (`stackLog_ge_of_announced`): every layout a stream
  announces stacks at least the smallest execution;
* its stream is at most `STREAM_CAP` scalars (`stream_le_of_verifyDeferred`: at most
  `leanVmStream = 4792`).

The openings disagree only on a Keccak-256 collision (`capsAgree_or_collide`), so the children of a
node `NodeRelation` admits are children the guest program accepts, or one of their proofs exhibits
a collision (`acceptableChildren_or_collide`), on every bytecode, the guest program's among them
(`guestChildren_acceptable_or_collide`).
-/

namespace LeanVM.Guest.Child

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash LeanVM.Node
open LeanVM.Guest.Completeness

@[expose] public section

/-- **A child the deferring verifier accepts, its openings agreeing at every query step, is one the
guest program accepts**, on every bytecode. -/
theorem acceptableChild_of_accepted {bytecode : List K} {seed : Digest} {child : Child}
    (hshape : child.statement.deferredClaim.HasBytecodeShape bytecode)
    (hv : verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
      child.proof = true)
    (hcaps : ∀ step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child),
      Limits.OpeningsAgree step.1 step.2) :
    AcceptableChild bytecode seed child where
  deferredClaimShaped := hshape
  verifies := hv
  stackLogAtLeastMinimum _ _ h := stackLog_ge_of_announced h
  streamWithinCap := stream_le_of_verifyDeferred hv
  capsAgree := hcaps

/-- **The children of a node `NodeRelation` admits are children the guest program accepts, or one
of their proofs exhibits a Keccak-256 collision**, on every bytecode. -/
theorem acceptableChildren_or_collide {bytecode : List K} {seed : Digest}
    {statement : NodeStatement} {witness : NodeWitness}
    (hrel : NodeRelation bytecode seed statement witness) :
    ChildrenOk bytecode seed witness ∨ ∃ child ∈ witness.children, OpeningsCollide child.proof := by
  refine or_iff_not_imp_right.mpr fun hc child hchild ↦ ?_
  obtain ⟨hshape, hv⟩ := hrel.2.2.1 child hchild
  exact acceptableChild_of_accepted hshape hv <|
    (capsAgree_or_collide bytecode seed child).resolve_right fun h ↦ hc ⟨child, hchild, h⟩

/-- **The guest program's form**: the children of a node `NodeRelation` admits on the guest
program's bytecode are children it accepts, or one of their proofs exhibits a Keccak-256
collision. -/
theorem guestChildren_acceptable_or_collide {seed : Digest} {statement : NodeStatement}
    {witness : NodeWitness} (hrel : NodeRelation (bytecodeWords guestProgram) seed statement witness) :
    (∀ child ∈ witness.children, AcceptableChild (bytecodeWords guestProgram) seed child) ∨
      ∃ child ∈ witness.children, OpeningsCollide child.proof :=
  acceptableChildren_or_collide hrel

end

end LeanVM.Guest.Child
