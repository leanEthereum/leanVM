module

public import Statement.LeanVmGuest
public import Statement.LeanVmGuestProver
public import Statement.LeanVmCompleteness

/-!
# The leanISA guest program: completeness

The guest program's completeness on the nodes within the deployed limits (`DeployedLimits`) whose
children the verifier accepts, unless a child's proof exhibits a Keccak-256 collision in its Merkle
openings (`OpeningsCollide`), its execution made from the statement and the witness
(`GuestExecutionComplete`). The soundness side, what a node proves, is `LeanVmGuest.lean`; the
batching's own soundness (`BatchingSound`) is `LeanVmGuestBatching.lean`. `lean_ethereum.py` is
`guests/lean_ethereum.py` and `aggregation/<module>.rs` is
`crates/aggregation/src/<module>.rs`.
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-! ## The deployed limits -/

/-- **The deployed limits**, where `NodeRelation` admits witnesses the guest program cannot run, and
the node's fixed capacities, within which its run fits `2^30` committed words. Implied by these
and `NodeRelation`, and so not limits of their own: a child's stack log at
most `30` and rate in `[1, 4]` (`readAnnouncedSizes`), at most one blob matrix checked directly
(`NodeWitness.daMatrix`), the bus depth at most `32`, the tables' heights at most `30`, and the
declared claims at most the claims held. -/
structure DeployedLimits (statement : NodeStatement) (witness : NodeWitness) : Prop where
  /-- A claim declared `n` times is held `n` times (`List.Subperm`: a sub-multiset), by raw
  signatures or by entries of the children's lists, each used once: each coverage slot is written
  once and the declared claims have one slot each (`main` in `lean_ethereum.py`; a child's list
  by hinted indices, `child_claims`, or by strictly increasing hinted gaps, every claim of the
  list writing one mark, `child_claims_mono`; the count of written slots, `main`), where
  `NodeRelation` lets two equal claims share one holder. -/
  claimsHeldWithMultiplicity :
    statement.claims.xmss.Subperm (witness.xmssSignatures.map (·.1) ++
      (witness.children.map (·.statement.claims.xmss)).flatten) ∧
    statement.claims.sphincs.Subperm (witness.sphincsSignatures.map (·.1) ++
      (witness.children.map (·.statement.claims.sphincs)).flatten)
  /-- At most `MAX_RECURSIONS` children (`Batch.maxRecursions`, `lean_ethereum.py`). -/
  atMostSixteenChildren : witness.children.length ≤ Batch.maxRecursions
  /-- At most `2^17` claims in the children's lists, in all. -/
  atMost2Pow17ChildClaims :
    (witness.children.map fun child ↦
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length).sum ≤ 2 ^ 17
  /-- At most `2048` raw leanXMSS signatures. -/
  atMost2048Xmss : witness.xmssSignatures.length ≤ 2048
  /-- At most `512` raw leanSPHINCS signatures. -/
  atMost512Sphincs : witness.sphincsSignatures.length ≤ 512
  /-- At most `LeanDa.maxRows` rows in the blob matrix checked directly. -/
  atMostMaxRows : ∀ p ∈ witness.daMatrix, p.2.rows.length ≤ LeanDa.maxRows

/-! ## The guest program's completeness

The guest program runs every node within the deployed limits, in at most `2^30` committed words,
whatever proofs its children carry, as long as `NodeRelation` has the verifier accept them, unless
a child's proof exhibits a Keccak-256 collision in its Merkle openings (`OpeningsCollide`). -/

namespace Limits

/-- The digest of a Merkle leaf: Keccak-256 of its words as bytes (`hash_leaf`,
`crates/verifier/src/merkle.rs`), the leaf an opening's climb starts from. -/
def _root_.LeanVM.Protocol.KeccakHash.merkleLeafDigest (words : List K) : Digest :=
  keccak256 (words.flatMap K.toBytes)

/-- The digest an opening's climb reaches from `node` at `leafPosition` over `path`. -/
def climbTo (node : Digest) (leafPosition : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccakF1600 node leafPosition path)

end Limits

namespace Completeness

/-! ### A collision in a child's openings

The guest program writes each node of a level's Merkle cap once, so two openings of one phase
meeting at a node must give it one digest. Two that give it different digests, both climbing to
the phase's root (`openPhase`), hash different bytes to one digest at some level of their climbs. -/

/-- **The bytes an opening's climb hashes at `level`** (`climb`): the node it has reached there and
the sibling its path carries, the left one first. -/
def climbInput (opening : Opening) (level : ℕ) : Bytes :=
  let node := Limits.climbTo (merkleLeafDigest opening.leaf) opening.leafIndex
    (opening.path.take level)
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
