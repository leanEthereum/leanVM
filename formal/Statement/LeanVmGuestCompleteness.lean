module

public import Statement.LeanVmGuest
public import Statement.LeanVmGuestProver

/-!
# The leanISA guest program: completeness

The guest program's completeness on the nodes within the deployed limits (`DeployedLimits`) whose
children the verifier accepts, unless a child's proof exhibits a Keccak-256 collision in its Merkle
openings (`OpeningsCollide`), its execution made from the statement and the witness
(`GuestExecutionComplete`). The soundness side is `LeanVmGuest.lean`. `lean_ethereum.py` is
`guests/lean_ethereum.py` and `aggregation/<module>.rs` is
`crates/aggregation/src/<module>.rs`.
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-! ## The deployed limits -/

/-- **The deployed limits**: the node's fixed capacities, within which its run fits `2^30`
committed words. Not limits of their own, as `NodeRelation` implies them: at most `maxRecursions`
children (`batch`), a child's stack log at most `30` and rate in `[1, 4]` (`readAnnouncedSizes`), at
most one blob matrix checked directly, of at most `LeanDa.maxRows` rows (`MatrixWitness.Opens`), the
bus depth at most `32` and the tables' heights at most `30`; with these limits, the declared claims
at most the claims held (`SignatureClaimsHeld`). -/
structure DeployedLimits (statement : NodeStatement) (witness : NodeWitness) : Prop where
  /-- At most `2^17` claims in the children's lists, in all. -/
  atMost2Pow17ChildClaims :
    (witness.children.map fun child ↦
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length).sum ≤ 2 ^ 17
  /-- At most `2048` raw leanXMSS signatures. -/
  atMost2048Xmss : witness.xmssSignatures.length ≤ 2048
  /-- At most `512` raw leanSPHINCS signatures. -/
  atMost512Sphincs : witness.sphincsSignatures.length ≤ 512

/-! ## The guest program's completeness

The guest program runs every node within the deployed limits, in at most `2^30` committed words,
whatever proofs its children carry, as long as `NodeRelation` has the verifier accept them, unless
a child's proof exhibits a Keccak-256 collision in its Merkle openings (`OpeningsCollide`). -/

namespace Completeness

/-! ### A collision in a child's openings

The guest program writes each node of a level's Merkle cap once, so two openings of one phase
meeting at a node must give it one digest. Two that give it different digests, both climbing to
the phase's root (`openPhase`), hash different bytes to one digest at some level of their climbs. -/

/-- **The bytes an opening's climb hashes at `level`** (`climb`): the node it has reached there and
the sibling its path carries, the left one first. -/
def climbInput (opening : Opening) (level : ℕ) : Bytes :=
  let node := Id.run do
    climb (m := Id) keccakF1600 (← merkleLeafDigestWith (m := Id) keccakF1600 opening.leaf)
      opening.leafIndex (opening.path.take level)
  let sibling := opening.path.getD level default
  if opening.leafIndex / 2 ^ level % 2 = 0 then digestBytes node ++ digestBytes sibling
  else digestBytes sibling ++ digestBytes node

/-- **A proof's openings exhibit a Keccak-256 collision**: two openings of one phase whose climbs
hash, at one level of their paths, different bytes to one digest. -/
def OpeningsCollide (proof : Proof) : Prop :=
  ∃ phase ∈ proof.openings, ∃ a ∈ phase, ∃ b ∈ phase, ∃ level < a.path.length,
    level < b.path.length ∧ climbInput a level ≠ climbInput b level ∧
      keccak256 (climbInput a level) = keccak256 (climbInput b level)

/-- **The guest's execution, made from the statement and the witness, on every node within the
deployed limits, or a collision in a child's openings**: for every statement and witness with
`NodeRelation` under the deployed seed (so the deferring verifier accepts every child's proof),
within the deployed limits (`DeployedLimits`), the executor's run of the guest program on the
advice made from the statement and the witness (`LeanVM.Guest.guestExecution`,
`LeanVmGuestProver.lean`) returns a valid execution of the guest program on the statement's digest,
of committed size at most `2^30`, the sizes the honest prover proves, or some child's proof
exhibits a Keccak-256 collision (`OpeningsCollide`). Proved by
`LeanVM.Guest.EndExec.guestExecution_complete_holds`. -/
def GuestExecutionComplete : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness →
    (∃ execution, guestExecution guestProgram statement witness = .ok execution ∧
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      execution.committedSize ≤ 2 ^ 30) ∨
    ∃ child ∈ witness.children, OpeningsCollide child.proof

end Completeness

end LeanVM.Guest

end
