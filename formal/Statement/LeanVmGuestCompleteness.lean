module

public import Statement.LeanVmGuest

/-!
# The leanISA guest program: completeness, and the batching's soundness

The guest program's completeness on the covered nodes whose children carry honest proofs
(`GuestCompleteOnHonestChildren`, within the deployed limits, `DeployedLimits`), the honest proof
rarely refused (`HonestProofRarelyRefused`), and the recursion step, the batching of the
children's deferred claims, sound in the random-permutation model (`BatchingSound`). The
soundness side, what a node proves, is `LeanVmGuest.lean`. `lean_ethereum.py:N` is line `N`
of `crates/rec_aggregation/guests/lean_ethereum.py`, `aggregation/<module>.rs:N` of
`crates/rec_aggregation/src/aggregation/<module>.rs`, at the pin (`../leanvm-rev`).
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-! ## The deployed limits -/

/-- **The coverage table's slots** (`n_total`, `lean_ethereum.py:4530`): one for each raw
signature and each entry of a child's signature lists, every slot written once
(`lean_ethereum.py:4564-4567`: the writes `:4590, 4595, 4179, 4247`, counted by `written`,
`:4614-4615, 4640-4641`). -/
def coverageSlots (witness : NodeWitness) : ℕ :=
  witness.xmssSignatures.length + witness.sphincsSignatures.length +
    (witness.children.map fun child ↦
      child.statement.claims.xmss.length + child.statement.claims.sphincs.length).sum

/-- **The deployed limits**, where `NodeRelation` admits witnesses the guest program cannot run.
Implied by these, with `NodeRelation` and honest children, and so not limits of their own: a child's
stack log at most `30` and rate in `[1, 4]` (`readAnnouncedSizes`), at most one blob matrix checked
directly (`NodeWitness.daMatrix`), every count of `meta` and of a child's lists below `2^20` (each at
most `coverageSlots`), the bus depth at most `32`, the tables' heights at most `30`. -/
structure DeployedLimits (statement : NodeStatement) (witness : NodeWitness) : Prop where
  /-- A claim declared `n` times is held `n` times (`List.Subperm`: a sub-multiset), by raw
  signatures or by entries of the children's lists, each used once: each coverage slot is written
  once and the declared claims have one slot each (`lean_ethereum.py:4589-4590, 4594-4595`; a
  child's list by hinted indices, `:4178-4179`, or by strictly increasing hinted gaps, every claim
  of the list writing one mark, `:4243-4247, 4301`; the count, `:4641`), where `NodeRelation` lets
  two equal claims share one holder. -/
  claimsHeldWithMultiplicity :
    statement.claims.xmss.Subperm (witness.xmssSignatures.map (·.1) ++
      (witness.children.map (·.statement.claims.xmss)).flatten) ∧
    statement.claims.sphincs.Subperm (witness.sphincsSignatures.map (·.1) ++
      (witness.children.map (·.statement.claims.sphincs)).flatten)
  /-- At most `MAX_RECURSIONS = 16` children (`lean_ethereum.py:4524`). -/
  atMostSixteenChildren : witness.children.length ≤ 16
  /-- The coverage table below `2^20` (`MAX_KEYS`, `crates/rec_aggregation/src/aggregation/mod.rs`, the
  host's cap; the guest program bounds it by its memory, every count being a memory address). -/
  coverageSlotsBelow2Pow20 : coverageSlots witness < 2 ^ 20

/-! ## The guest program's completeness on the covered nodes -/

namespace Completeness

/-- **The nodes the deployed budget covers**, seven families by the node's children, raw
signatures, the rows of the blob matrix checked directly, and coverage slots (`coverageSlots`: the
raw signatures and the children's claims): a recursion node of `2048` slots; a leaf of `2048` raw
signatures; `8` children and `2^15` slots; `4` children, `1024` raw signatures and `8192` slots;
`4` children, a matrix of `32` rows and `8192` slots; `2` children, `256` raw signatures, a matrix
of `32` rows and `8192` slots; `2` children, a matrix of `32` rows and `2^14` slots. A node of no
child and no raw signature, so of no claim, with a matrix of `32` rows, is of the fifth. The raw
signatures are counted with a leanSPHINCS signature as three (`raw`): its check costs the guest
program about three leanXMSS ones (at leanVM `40f877dc`, `899` `KECCAK`s against `398`, `8582`
memory words against `1551`). -/
def CoveredNode (witness : NodeWitness) : Prop :=
  let n := witness.children.length
  let raw := witness.xmssSignatures.length + 3 * witness.sphincsSignatures.length
  let blobs := (witness.daMatrix.map fun _ ↦ 1).getD 0
  let rows := (witness.daMatrix.map fun p ↦ p.2.rows.length).getD 0
  let slots := coverageSlots witness
  (raw = 0 ∧ blobs = 0 ∧ slots ≤ 2048) ∨
  (n = 0 ∧ blobs = 0 ∧ raw ≤ 2048 ∧ slots ≤ 2048) ∨
  (n ≤ 8 ∧ raw = 0 ∧ blobs = 0 ∧ slots ≤ 2 ^ 15) ∨
  (n ≤ 4 ∧ raw ≤ 1024 ∧ blobs = 0 ∧ slots ≤ 8192) ∨
  (n ≤ 4 ∧ raw = 0 ∧ rows ≤ 32 ∧ slots ≤ 8192) ∨
  (n ≤ 2 ∧ raw ≤ 256 ∧ rows ≤ 32 ∧ slots ≤ 8192) ∨
  (n ≤ 2 ∧ raw = 0 ∧ rows ≤ 32 ∧ slots ≤ 2 ^ 14)

/-! ### Children carrying honest proofs

The guest program checks a child with the deployed Keccak, so the honest proof is made with it
(the honest prover in `Id` over `keccakF1600`); what it can fail by (a proof of work without a
nonce within its fuel, a zero challenge where the guest program divides) is bounded in the
random-permutation model for the same prover and check (`verifierRefusingZero`).

The guest program divides by some of the verifier's challenges (the WHIR fold and tail challenges
and each level's batching challenge `λ`, `lean_ethereum.py:1400, 1709, 1714`), so a zero one makes
it reject a child the verifier accepts; the honest child's hypothesis refuses a zero challenge
anywhere (`VerifierProgram.refusingZeroChallenge`), a slightly stronger one, each challenge being
zero with probability `2^-192`. -/

/-- **`program` refusing a zero challenge**: every sampled challenge `0` fails. -/
def _root_.LeanVM.Protocol.Compile.VerifierProgram.refusingZeroChallenge {α : Type} :
    VerifierProgram α → VerifierProgram α
  | .ret a => .ret a
  | .fail => .fail
  | .read k => .read fun x ↦ (k x).refusingZeroChallenge
  | .sample k => .sample fun x ↦ if x = 0 then .fail else (k x).refusingZeroChallenge
  | .grind bits k => .grind bits k.refusingZeroChallenge
  | .commit height width k => .commit height width k.refusingZeroChallenge
  | .query i ps k => .query i ps fun rows ↦ (k rows).refusingZeroChallenge

/-- **The leanVM verifier refusing a zero challenge** (`VerifierProgram.refusingZeroChallenge`):
`leanVmVerifier π` with every sampled challenge `0` a failure. -/
def verifierRefusingZero {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← spongeSeedWith π (bytecodeWords program) (publicInputDigest input)
  runProof π
    (leanVmVerifierProgram (bytecodeWords program) (publicInputDigest input)).refusingZeroChallenge
        seed proof

open OracleComp OracleSpec in
/-- **The honest proof is rarely refused**: in the random-permutation model, at `2^25` nonces per
proof of work, the honest prover `LeanVM.leanVmHonestProver` (`LeanVm.lean`, `LeanVM.Prover.prove`)
makes no proof, or `verifierRefusingZero` rejects its proof, of a valid execution of committed size
at most `2^30`, at an inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`, with probability at most `2^-126`. -/
def HonestProofRarelyRefused : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 →
    1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← LeanVM.leanVmHonestProver Common.queryPermutation program input execution ρ (2 ^
            25) with
        | none => pure false
        | some proof =>
          verifierRefusingZero Common.queryPermutation program input proof)}[accepted = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 126

/-- **A child carrying an honest proof**: its fresh claim on the bytecode is true, and its proof
is the honest prover's, with the deployed Keccak, of an execution of the guest program on its
statement's digest under the deployed seed, and the leanVM verifier refusing a zero challenge
accepts it. No size is asked: the guest program has an opening arm for every stack log the
verifier admits of an execution of its bytecode, from `20` (`min_execution_stacked_log`,
`crates/verifier`'s `layout.rs`: the bytecode's `2^19` instructions alone fill `2^19` words) to `30`
(`MAX_STACKED_LOG`), and the
honest prover makes no proof past `2^30` committed words (`maxCommitted`). `lean_vm` proves that
such a child meets what the guest program checks of a child (`guest_child_complete`). -/
def HonestChild (child : Child) : Prop :=
  let input := PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) child.statement)
  child.freshClaim.Holds (bytecodeWords guestProgram) ∧
    ∃ (execution : Execution guestProgram) (ρ : ℕ),
      LeanVM.leanVmHonestProver (m := Id) keccakF1600 guestProgram input execution ρ (2 ^ 25) =
        some child.proof ∧
      verifierRefusingZero (m := Id) keccakF1600 guestProgram input child.proof = true

/-- **Every covered node whose children carry honest proofs has a valid execution of the guest
program**: for every statement and witness with `NodeRelation` under the deployed seed, within the
deployed limits, in one of the families `CoveredNode` lists, every child carrying an honest proof
(`HonestChild`), there is a valid execution of the guest program on the statement's digest of
committed size at most `2^30`, the sizes the honest prover proves and `HonestProofRarelyRefused`
covers. Reading `HonestProofRarelyRefused` for the deployed Keccak,
so that the honest proof is a `HonestChild`, is the heuristic that the deployed Keccak-f[1600]
behaves as a random permutation, applied to this prover. Proved by
`LeanVM.Guest.Completeness.guest_complete_on_honest_children`. -/
def GuestCompleteOnHonestChildren : Prop :=
  ∀ (statement : NodeStatement) (witness : NodeWitness),
    NodeRelation (bytecodeWords guestProgram) (deployedSeed guestProgram) statement witness →
    DeployedLimits statement witness → CoveredNode witness →
    (∀ child ∈ witness.children, HonestChild child) →
    ∃ execution : Execution guestProgram,
      ValidExecution guestProgram
        (PublicInput.ofDigest (statementDigest (deployedSeed guestProgram) statement)) execution ∧
      execution.committedSize ≤ 2 ^ 30

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
noncomputable def batchingProgram (deferredClaimCheck : DeferredClaim → Prop) (bytecode : List K)
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
(`DeferredClaim.HoldsWithShape`). -/
noncomputable def boundedBatchingProgram (childCountBound : ℕ) (bytecode : List K) :
    VerifierProgram Bool := do
  let childCount ← readChildCount childCountBound
  batchingProgram (DeferredClaim.HoldsWithShape bytecode) bytecode childCount

/-- The proof's stream begins with the count's cells and those of fewer than `childCountBound`
children of the bytecode's shapes, one of whose claims is false: its proof's claim's value
(`BytecodeClaim.Holds`) or its statement's claim (`DeferredClaim.HoldsWithShape`; with the shapes
given, it adds only that the bytecode's length is a power of two, which `BatchingSound`
assumes). -/
def SomeChildClaimFalse (bytecode : List K) (childCountBound : ℕ) (proof : Proof) : Prop :=
  ∃ children : List ChildClaims, children.length < childCountBound ∧
    (∀ child ∈ children, ChildHasBytecodeShape bytecode child) ∧
    cellsBeforeChallenge children <+: proof.stream ∧
    ¬ ∀ child ∈ children,
      child.freshClaim.Holds bytecode ∧ child.carriedClaim.HoldsWithShape bytecode

/-- **The batching program's query bound** on child counts below `childCountBound`: the seed's two
queries, then a quarter of the program's cost (the count, the children's cells, the challenge, the
sumcheck's rounds and the final value). -/
def batchingQueryBound (bytecode : List K) (childCountBound : ℕ) : ℕ :=
  2 + (rateScalars + (childCountBound * (childWordCount (Nat.log2 bytecode.length) +
    zerosToWholeRate (childWordCount (Nat.log2 bytecode.length))) + 4 + 6 * Nat.log2
      bytecode.length + 1)) / 4

open OracleComp OracleSpec in
/-- **The batching in the random-permutation model.** For a bytecode of power-of-two length and
a bound `M ≤ 2^64 - 1` on the children's count: an adversary of `QA` queries to `π` and `π⁻¹`
outputs a proof; the probability that the batching's verifier over `π` (Keccak-256 the sponge over
`π`) accepts it while its stream begins with fewer than `M` children of the bytecode's shapes one
of whose claims is false is at most `(QA + QV + 1) · M · 2^-191 + 5 (QA + QV)² · 2^-256`, for
`QA ≤ 2^128` and the program's query bound `QV = batchingQueryBound bytecode M ≤ 2^96`; the
adversary's private coins are free. The factor `M` is the batching's one challenge `λ`: the
children's `2n` claims, `n < M`, are combined with its powers, and a nonzero combination of degree
below `2M` vanishes at fewer than `2M` values of `λ` (a sumcheck round's challenge at at most `2`).

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
      (((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) + 1) * M * (2 : ℝ≥0∞)⁻¹ ^ 191 +
        5 * ((QA + batchingQueryBound bytecode M : ℕ) : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

end Batch

end LeanVM.Guest

end
