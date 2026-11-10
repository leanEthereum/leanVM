/-
  LeanVM.Guest.AcceptableChild

  What the guest program checks of a child (`AcceptableChild`), and the guest program's
  completeness stated with it (`GuestCompleteCovered`, `GuestChildComplete`): the statement's
  completeness on honest children (`GuestCompleteOnHonestChildren`) follows from them.
-/

module

public import Statement.LeanVmGuestCompleteness
public import LeanVM.Protocol.Compile.RunPure
public import LeanVM.Guest.Coverage

/-!
# A child the guest program accepts

`Statement/LeanVmGuestCompleteness.lean` states the guest program's completeness for children
carrying honest proofs (`HonestChild`). The proofs go through what the guest program checks of a
child, defined here: `ChildrenProven`'s two conditions, a stack log at least `MU_MIN = 22`, a proof
stream of at most `STREAM_CAP = 8192` scalars, its openings agreeing in the guest program's Merkle
caps, and no zero challenge (`AcceptableChild`). `GuestCompleteCovered` is the guest program's
completeness on covered nodes whose children are acceptable, for every seed, and
`GuestChildComplete` says that an honest proof is an acceptable child (`G:N` is line `N` of
`crates/rec_aggregation/guests/lean_ethereum.py`, `aggregation/<module>.rs:N` of
`crates/rec_aggregation/src/aggregation/<module>.rs`, at the pin).
-/

@[expose] public section

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

namespace Coverage

/-- `STREAM_CAP` (`aggregation/child.rs:268`): a child's proof stream is zero-padded to it. -/
def childStreamCap : ℕ := 8192

/-- `MU_MIN` (`aggregation/child.rs:259`): the least stack log the guest program has an opening arm
for. -/
def minChildStackLog : ℕ := 22

/-- The deferring verifier's initial state on a child's proof under the node's seed
(`verifyDeferredWith`). -/
def childVerifierStart (seed : Digest) (child : Child) : VerifierProgramState :=
  ⟨⟨keccakF1600 (seedInput seed (statementDigest seed child.statement)), [], none⟩,
    child.proof.stream,
    child.proof.openings, []⟩

end Coverage

namespace Limits

/-- **The deployed deferring verifier refusing a zero challenge**
(`VerifierProgram.refusingZeroChallenge`):
`verifyDeferred` with every sampled challenge `0` a failure. -/
def verifyDeferredRefusingZero (bytecode : List K) (iv publicInput : Digest)
    (claim : BytecodeClaim) (proof : Proof) : Bool :=
  Id.run (runProof (m := Id) keccakF1600
    (deferringVerifierProgram claim bytecode publicInput).refusingZeroChallenge
    (keccakF1600 (seedInput iv publicInput)) proof)

/-- **The query steps of a run** of the compiled verifier (Keccak-256, Keccak-f[1600]): each
`query` step as its tree's height and its positions, each with its opening in the phase it
consumes. -/
def queryStepsOf {α : Type} : VerifierProgram α → VerifierProgramState → List (ℕ × List (ℕ ×
    Opening))
  | .ret _, _ => []
  | .fail, _ => []
  | .read k, state => match state.stream, state.sponge.ground with
    | x :: xs, none =>
      queryStepsOf (k x) { state with
        sponge := Id.run (absorb keccakF1600 state.sponge x dsObserve), stream := xs }
    | _, _ => []
  | .sample k, state =>
    let (c, sponge) := Id.run (squeeze keccakF1600 state.sponge)
    queryStepsOf (k c) { state with sponge := sponge }
  | .grind bits k, state => match state.stream, state.sponge.ground with
    | n :: xs, none =>
      let (pow, sponge) := Id.run (absorbNonce keccakF1600 state.sponge n)
      if powOk bits pow then queryStepsOf k { state with sponge := sponge, stream := xs } else []
    | _, _ => []
  | .commit height width k, state => match state.stream, state.sponge.ground with
    | x0 :: x1 :: xs, none =>
      queryStepsOf k { state with
        sponge :=
          Id.run (absorb keccakF1600
            (Id.run (absorb keccakF1600 state.sponge x0 dsObserve)) x1 dsObserve)
        stream := xs
        roots := state.roots ++ [(digestFromHalves (x0, x1), height, width)] }
    | _, _ => []
  | .query i ps k, state => match state.roots[i]?, state.openings with
    | some (root, height, width), phase :: rest =>
      match Id.run (openPhase (m := Id) keccakF1600 root height width ps phase) with
      | some rows => (height, ps.zip phase) :: queryStepsOf (k rows) { state with openings := rest }
      | none => []
    | _, _ => []

/-- The heap index of the node at `level` (the leaves at `0`) above the leaf `leafPosition` of a
tree of height `depth`. -/
def merkleHeapIndex (depth leafPosition level : ℕ) : ℕ :=
  2 ^ (depth - level) + leafPosition / 2 ^ level

/-- The heap index of the sibling of the node at `level < depth` above the leaf `leafPosition`. -/
def siblingHeapIndex (depth leafPosition level : ℕ) : ℕ :=
  2 * merkleHeapIndex depth leafPosition (level + 1) + (!leafPosition.testBit level).toNat

/-- The digest of a Merkle leaf: Keccak-256 of its words as bytes (`hash_leaf`,
`crates/verifier/src/merkle.rs:13-15`), the leaf an opening's climb starts from. -/
def _root_.LeanVM.Protocol.KeccakHash.merkleLeafDigest (words : List K) : Digest :=
  keccak256 (words.flatMap K.toBytes)

/-- The digest an opening's climb reaches from `node` at `leafPosition` over `path`. -/
def climbTo (node : Digest) (leafPosition : ℕ) (path : List Digest) : Digest :=
  Id.run (climb (m := Id) keccakF1600 node leafPosition path)

/-- **The opening `queryOpening` gives the heap node `heapNode` the digest `digest`**: the node is
on its climb, with the climb's digest there, or is the sibling it carries at a level. -/
def OpeningGivesNode (depth : ℕ) (queryOpening : ℕ × Opening) (heapNode : ℕ) (digest : Digest) :
    Prop :=
  (∃ level ≤ depth, heapNode = merkleHeapIndex depth queryOpening.1 level ∧
    digest = climbTo (merkleLeafDigest queryOpening.2.leaf) queryOpening.1
      (queryOpening.2.path.take level)) ∨
  ∃ level < depth, heapNode = siblingHeapIndex depth queryOpening.1 level ∧
    digest = queryOpening.2.path.getD level default

/-- The openings of one query step agree wherever they meet. -/
def OpeningsAgree (depth : ℕ) (queryOpenings : List (ℕ × Opening)) : Prop :=
  ∀ a ∈ queryOpenings, ∀ b ∈ queryOpenings, ∀ heapNode digest digest',
    OpeningGivesNode depth a heapNode digest → OpeningGivesNode depth b heapNode digest' →
      digest = digest'

end Limits

/-- **A child the guest program accepts** under the seed `seed`: what the guest program asks of
each child, `ChildrenProven`'s two conditions and the deployed ones:
* its stack log is at least `MU_MIN = 22`: the guest program has one opening arm per stack log in
  `[22, 28]` (G:3491-3493); the verifier admits stack logs from `Whir.minLogStack`;
* its proof stream is at most `STREAM_CAP = 8192` scalars (G:3338-3339);
* its openings agree in the guest program's Merkle caps: at every query step of its deferring
  verifier, run under the node's seed, the step's openings agree wherever they meet (one tree's
  openings, the honest prover's, agree);
* no zero challenge: the deferring verifier refusing a zero challenge anywhere accepts its proof
  (`verifyDeferredRefusingZero`), as the guest program divides by some (the WHIR fold and tail
  challenges and each level's batching challenge `λ`, G:1400, 1709, 1714). -/
structure AcceptableChild (bytecode : List K) (seed : Digest) (child : Child) : Prop where
  /-- Its deferred claim has the bytecode's shape. -/
  deferredClaimShaped : child.statement.deferredClaim.HasBytecodeShape bytecode
  /-- The deferring verifier accepts its proof. -/
  verifies : verifyDeferred bytecode seed (statementDigest seed child.statement) child.freshClaim
    child.proof = true
  /-- Its stack log is at least `MU_MIN = 22`. -/
  stackLogAtLeastMinimum : ∀ layout r, announcedLayoutAndRate bytecode child.proof.stream = some
      (layout, r) →
    Coverage.minChildStackLog ≤ layout.stackLog
  /-- Its proof stream is at most `STREAM_CAP = 8192` scalars. -/
  streamWithinCap : child.proof.stream.length ≤ Coverage.childStreamCap
  /-- Its openings agree in the guest program's Merkle caps. -/
  capsAgree : ∀ step ∈ Limits.queryStepsOf
      (deferringVerifierProgram child.freshClaim bytecode (statementDigest seed child.statement))
        (Coverage.childVerifierStart seed child),
    Limits.OpeningsAgree step.1 step.2
  /-- The deferring verifier refusing a zero challenge accepts its proof. -/
  noZeroChallenge : Limits.verifyDeferredRefusingZero bytecode seed
    (statementDigest seed child.statement) child.freshClaim child.proof = true

namespace Completeness

open Coverage

/-- **Every covered node has a valid execution of the leanISA guest program**: for every seed,
statement and witness with `NodeRelation`, within the deployed limits (so at most `16` children),
every child one the guest program accepts (`AcceptableChild`: at one of its opening arms, its
openings agreeing in the caps, no zero challenge), and in one of the families `CoveredNode` lists,
there is a valid execution of the guest program on the statement's digest of committed size in
`[2^22, 2^28]`. Proved by `LeanVM.Guest.Budget.guest_complete_covered`. -/
abbrev GuestCompleteCovered : Prop :=
  ∀ (seed : Digest) (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) seed statement witness →
    DeployedLimits statement witness →
    (∀ child ∈ witness.children, AcceptableChild (bytecodeWords guestProgram) seed child) →
    CoveredNode witness →
    ∃ execution : Execution guestProgram,
      ValidExecution guestProgram (PublicInput.ofDigest (statementDigest seed statement))
        execution ∧
      2 ^ 22 ≤ execution.committedSize ∧ execution.committedSize ≤ 2 ^ 28

/-- **An honest prover's proof over the deployed Keccak-f[1600]**, the hash Keccak-256, if it
makes one (`HonestChild`'s, `Statement/LeanVmGuestCompleteness.lean`, written out). -/
def honestProofWithDeployedKeccak (honestProver : HonestProver) (program : LeanIsaProgram)
    (input : PublicInput) (execution : Execution program) (ρ nonceAttemptsPerProofOfWork : ℕ) :
    Option Proof :=
  honestProver (m := Id) keccakF1600 program input execution ρ nonceAttemptsPerProofOfWork

/-- **The honest proof of an execution of the guest program is a child the guest program
accepts**:
1. it is rarely refused (`HonestProofRarelyRefused`);
2. its proof with the deployed Keccak (`honestProofWithDeployedKeccak`), if it makes one, of an
   execution of the guest program of committed size above `2^21` on a statement's digest under
   the deployed seed, wherever `verifierRefusingZero` with the deployed Keccak accepts it, forms
   with the statement (its deferred claim shaped) and some claim `fresh` on the bytecode whose
   value is true (`BytecodeClaim.Holds`) a child the guest program accepts (`AcceptableChild`).
Proved by `LeanVM.Guest.Budget.guest_child_complete`. -/
def GuestChildComplete : Prop :=
  HonestProofRarelyRefused ∧
  ∀ (statement : NodeStatement) (execution : Execution guestProgram) (ρ : ℕ),
    2 ^ 21 < execution.committedSize →
    statement.deferredClaim.HasBytecodeShape (bytecodeWords guestProgram) →
    let input := PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)
    ∀ proof, honestProofWithDeployedKeccak LeanVM.leanVmHonestProver guestProgram input execution ρ
        (2 ^ 33) =
      some proof →
    verifierRefusingZero (m := Id) keccakF1600 guestProgram input proof = true →
    ∃ fresh, fresh.Holds (bytecodeWords guestProgram) ∧
      AcceptableChild (bytecodeWords guestProgram) (deployedSeed guestProgram)
        ⟨statement, fresh, proof⟩

end Completeness

end LeanVM.Guest

end
