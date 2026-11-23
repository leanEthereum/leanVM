module

public import Statement.LeanVmGuest
public import Statement.LeanVmGuestProver

/-!
# The leanISA guest program: completeness, and the batching's soundness

The guest program's completeness on the nodes within the deployed limits (`DeployedLimits`) whose
children the verifier accepts, unless a child's proof exhibits a Keccak-256 collision in its Merkle
openings (`OpeningsCollide`), its execution made from the statement and the witness
(`GuestExecutionComplete`), and the recursion step, the batching of the children's deferred
claims, sound in the random-permutation model (`BatchingSound`). The soundness side, what a node
proves, is `LeanVmGuest.lean`. `lean_ethereum.py` is
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

/-! ## The recursion step: the batching in the random-permutation model

The batching program with the count, below a bound, and the children read off the proof's stream
(a node's batching, `nodeBatchingProgram`, knows its children) and the check that the deferred
claim holds of the bytecode (`boundedBatchingProgram`), run on a proof an adversary outputs,
querying `π` and `π⁻¹`; the batching has no statement of its own. -/

namespace Batch

/-- A child has the bytecode's shapes: its proof's claim and its statement's are at points of
`log₂` of the bytecode's length. -/
def ChildHasBytecodeShape (bytecode : List K) (child : ChildClaims) : Prop :=
  child.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length ∧
    child.carriedClaim.HasBytecodeShape bytecode

/-- The words of a child at `bytecodeVariableCount` bytecode coordinates: its public input's two,
its proof's claim, its statement's claim. -/
def childWordCount (bytecodeVariableCount : ℕ) : ℕ :=
  2 + (bytecodeVariableCount + 1) + (bytecodeVariableCount + 1)

/-- A child read off its words (`ChildClaims.words`); `none` where the public input does not
decode. -/
def parseChild (bytecodeVariableCount : ℕ) (words : List E) : Option ChildClaims := do
  let publicInput ← digestFromHalves (words.getD 0 0, words.getD 1 0)
  let claimWords := words.drop 2
  let carriedWords := claimWords.drop (bytecodeVariableCount + 1)
  return ⟨publicInput,
    ⟨claimWords.take bytecodeVariableCount, claimWords.getD bytecodeVariableCount 0⟩,
    ⟨carriedWords.take bytecodeVariableCount, carriedWords.getD bytecodeVariableCount 0⟩⟩

/-- Read a child: its words, then the zeros to a whole rate. -/
def readChild (bytecodeVariableCount : ℕ) : VerifierProgram ChildClaims := do
  let wordCount := childWordCount bytecodeVariableCount
  let words ← VerifierProgram.readScalars (wordCount + zerosToWholeRate wordCount)
  VerifierProgram.require (words.drop wordCount = List.replicate (zerosToWholeRate wordCount) 0)
  liftOption (parseChild bytecodeVariableCount words)

/-- Read `childCount` children. -/
def readChildren (bytecodeVariableCount : ℕ) : (childCount : ℕ) → VerifierProgram (List ChildClaims)
  | 0 => pure []
  | childCount + 1 => do
    let child ← readChild bytecodeVariableCount
    let children ← readChildren bytecodeVariableCount childCount
    return child :: children

/-- **The batching of `childCount` children read off the stream.** -/
noncomputable def batchingProgram (deferredClaimCheck : DeferredBytecodeClaim → Prop) (bytecode : List K)
    (childCount : ℕ) : VerifierProgram Bool := do
  let children ← readChildren (Nat.log2 bytecode.length) childCount
  batchingAfterChildren deferredClaimCheck bytecode children

open Classical in
/-- The count below `childCountBound` whose power of the generator is `x`, if any. -/
noncomputable def childCountOfGeneratorPower (childCountBound : ℕ) (x : E) : Option ℕ :=
  if h : ∃ n, n < childCountBound ∧ Verifier.gpow n = x then some (Nat.find h) else none

/-- Read the count: `g^n`, then three zeros. -/
noncomputable def readChildCount (childCountBound : ℕ) : VerifierProgram ℕ := do
  let words ← VerifierProgram.readScalars rateScalars
  VerifierProgram.require (words.drop 1 = List.replicate (rateScalars - 1) 0)
  liftOption (childCountOfGeneratorPower childCountBound (words.getD 0 0))

/-- **The batching as a verifier program**, of fewer than `childCountBound` children: the count,
then the batching of that many, its deferred claim true of `bytecode`, shape and length included
(`DeferredBytecodeClaim.HoldsWithShape`). -/
noncomputable def boundedBatchingProgram (childCountBound : ℕ) (bytecode : List K) :
    VerifierProgram Bool := do
  let childCount ← readChildCount childCountBound
  batchingProgram (DeferredBytecodeClaim.HoldsWithShape bytecode) bytecode childCount

/-- The proof's stream begins with the count's cells and those of fewer than `childCountBound`
children of the bytecode's shapes, one of whose claims is false: its proof's claim's value
(`BytecodeClaim.Holds`) or its statement's claim (`DeferredBytecodeClaim.HoldsWithShape`; with the shapes
given, it adds only that the bytecode's length is a power of two, which `BatchingSound`
assumes). -/
def SomeChildClaimFalse (bytecode : List K) (childCountBound : ℕ) (proof : Proof) : Prop :=
  ∃ children : List ChildClaims, children.length < childCountBound ∧
    (∀ child ∈ children, ChildHasBytecodeShape bytecode child) ∧
    cellsBeforeChallenge children <+: proof.stream ∧
    ¬ ∀ child ∈ children,
      child.freshClaim.Holds bytecode ∧ child.carriedClaim.HoldsWithShape bytecode

/-- **The batching program's query bound** on child counts below `childCountBound`: the seed's two
queries, then a quarter of the program's cost (the count, the children's cells, the proof of work
and the challenge, the sumcheck's rounds and the final value). -/
def batchingQueryBound (bytecode : List K) (childCountBound : ℕ) : ℕ :=
  2 + (rateScalars + (childCountBound * (childWordCount (Nat.log2 bytecode.length) +
    zerosToWholeRate (childWordCount (Nat.log2 bytecode.length))) + 5 + 4 + 6 * Nat.log2
      bytecode.length + 1)) / 4

open OracleComp OracleSpec in
/-- **The batching in the random-permutation model.** For a bytecode of power-of-two length and
a bound `M ≤ 2^64 - 1` on the children's count: an adversary of `QA` queries to `π` and `π⁻¹`
outputs a proof; the probability that the batching's verifier over `π` (Keccak-256 the sponge over
`π`) accepts it while its stream begins with fewer than `M` children of the bytecode's shapes one
of whose claims is false is at most `(QA + QV + 1) · max(2M - 3, 8) · 2^-130 + 5 (QA + QV)² · 2^-256`,
for `QA ≤ 2^128` and the program's query bound `QV = batchingQueryBound bytecode M ≤ 2^96`; the
adversary's private coins are free. The factor `max(2M - 3, 8) · 2^-130` bounds each query's chance at
a challenge: a sumcheck round's is bad at no more than `2` values, `2/|E| = 8 · 2^-130`; the
batching's one challenge `λ` combines the children's `2n` claims, `n < M`, with its powers, a
nonzero combination of degree at most `2M - 3` vanishes at no more than `2M - 3` values of `λ`, and
a query reaches `λ` only by passing the proof of work of `batchLambdaGrindBits` bits before it, `2`
at `maxRecursions = 16`.

This is the batching run outside the circuit, with Keccak-f[1600] = `π`; it does not compose with
the guest program's in-circuit statements, whose `KECCAK` instruction computes the deployed
Keccak-f[1600], so soundness across recursion levels does not follow from it. -/
def BatchingSound : Prop :=
  ∀ (M : ℕ) (bytecode : List K), bytecode.length = 2 ^ Nat.log2 bytecode.length →
    M ≤ 2 ^ 64 - 1 →
    ∀ (adversary : OracleComp Common.RandomPermutationOracles (Unit × Proof)) (QA : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost QA → QA ≤ 2 ^ 128 →
    batchingQueryBound bytecode M ≤ 2 ^ 96 →
    Pr{let outcome ← Common.runWithRandomPermutation (do
         let output ← adversary
         let accepted ←
           runBatching Common.queryPermutation (boundedBatchingProgram M bytecode) output.2
         return (output, accepted))}[
      outcome.2 = true ∧ SomeChildClaimFalse bytecode M outcome.1.2] ≤
      (((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * (max (2 * M - 3) 8 : ℕ) *
          (2 : ℝ≥0∞)⁻¹ ^ 130 +
        5 * ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end Batch

end LeanVM.Guest

end
