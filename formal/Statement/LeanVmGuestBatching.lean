module

public import Statement.Verifier.Lib
public import Statement.RandomPermutation

/-!
# The leanISA guest program: the batching of the children's claims

The batching program `LeanVmGuest.lean`'s `DeferredClaimBatched` runs, transcribed: the claim a
node defers on the guest program's bytecode (`DeferredBytecodeClaim`), what a node knows of each child
(`ChildClaims`), and the batching of the children's deferred claims as a program of the verifier's
language (`Batch.nodeBatchingProgram`), and the batching's soundness on its own, outside the
circuit, in the random-permutation model (`Batch.BatchingSound`). Reference material: a first
reading takes the program as the batching of `crates/aggregation/src/deferred.rs` and looks things
up here.

Transcribed from leanVM: the modules of
`crates/aggregation/src/` and `guests/lean_ethereum.py`,
cited by their items' names.
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The deferred claim -/

/-- The claim a statement defers on the stacked bytecode: its value at a point (`DeferredBytecodeClaim`,
`crates/aggregation/src/deferred.rs`), the shape of a proof's claim (`BytecodeClaim`). -/
abbrev DeferredBytecodeClaim : Type := BytecodeClaim

/-- The cells a deferred claim is hashed and absorbed as, and a proof's claim on the bytecode
exported as: the point, then the value (`DeferredBytecodeClaim::cells`,
`crates/aggregation/src/deferred.rs`; the guest program's `defer_stmt`, and `verify_sub`'s
`defer_out`, `lean_ethereum.py`). -/
def DeferredBytecodeClaim.cells (claim : DeferredBytecodeClaim) : List E :=
  claim.bytecodePoint ++ [claim.bytecodeValue]

/-- The deferred claim has the shape of the bytecode `bytecode`: a point of `log₂` of its length
(`bytecode_vars`, `crates/aggregation/src/deferred.rs`; `BYTECODE_VARS`, `lean_ethereum.py`). -/
def DeferredBytecodeClaim.HasBytecodeShape (bytecode : List K) (claim : DeferredBytecodeClaim) : Prop :=
  claim.bytecodePoint.length = Nat.log2 bytecode.length

/-- **The deferred claim is true** of the bytecode `bytecode`: it has the shape, and the value is
the bytecode's multilinear extension at the point (`DeferredBytecodeClaim::recompute`,
`crates/aggregation/src/deferred.rs`). The length being `2 ^ len` is part of it: `HasBytecodeShape`
reads `Nat.log2` of the length, which a bytecode of other length shares, and the extension is of
`2 ^ len` values. Stronger than `BytecodeClaim.Holds` (the value only). The deployed outer verifier
checks it of the root's deferred claim (`AggregateProof::verify`,
`crates/aggregation/src/proof.rs`). -/
def DeferredBytecodeClaim.HoldsWithShape (bytecode : List K) (claim : DeferredBytecodeClaim) : Prop :=
  claim.HasBytecodeShape bytecode ∧ 2 ^ claim.bytecodePoint.length = bytecode.length ∧
    multilinearEval (bytecode.map ofK) claim.bytecodePoint = claim.bytecodeValue

/-! ## The batching program

The batching of the children's deferred claims (`aggregate_claims`, `lean_ethereum.py`;
`aggregate_deferred_claims`, `crates/aggregation/src/deferred.rs`), as a program of the verifier's
language (`VerifierProgram`): the cells absorbed before the challenge (`cellsBeforeChallenge`: the
count `n` as `g^n`, then each child's words, each padded with zeros to a whole rate), then a proof of
work of `batchLambdaGrindBits` bits and one challenge, whose powers are the lambdas, the sumcheck's `log₂ |bytecode|` rounds
(`sumcheckRoundsProgram`) and the final value, accepted if the final claim is the value times the
batched weight and the deferred claim meets a check (`batchingAfterChildren`); run from the batching
transcript's seed (`runBatching`). -/

/-- What a node knows of one child: the child's public input, the claim its proof makes
(`freshClaim`), and the claim its statement defers (`carriedClaim`). -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- The claim the child's proof makes. -/
  freshClaim : BytecodeClaim
  /-- The claim the child's statement defers. -/
  carriedClaim : DeferredBytecodeClaim

/-- The words the batching absorbs of a child: its public input's two cells, its proof's claim,
the claim its statement defers (`AGG_CHILD_WORDS`, `lean_ethereum.py`). -/
def ChildClaims.words (child : ChildClaims) : List E :=
  [(digestHalves child.publicInput).1, (digestHalves child.publicInput).2] ++
    DeferredBytecodeClaim.cells child.freshClaim ++ child.carriedClaim.cells

/-- The prover's part of a batching: the nonce of the proof of work before the challenge, the
sumcheck's rounds and the bytecode's value at its end (`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchingHints where
  /-- The nonce of the proof of work before the batching challenge, sent only if it is of nonzero
  bits (`Batch.lambdaGrindNonceCells`). -/
  lambdaGrindNonce : E
  /-- Each round's message `(g(1), g(∞))`. -/
  sumcheckMessages : List (E × E)
  /-- The bytecode's value at the sumcheck's final point. -/
  finalBytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`,
`crates/aggregation/src/deferred.rs`). -/
def batchingLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

end LeanVM.Node

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- The most children a node has, the arity of an aggregation tree (`MAX_RECURSIONS`,
`crates/aggregation/src/lib.rs`, which the guest program's `MAX_RECURSIONS`, `lean_ethereum.py`, is
set to). -/
def maxRecursions : ℕ := 16

/-- The bits of the proof of work before the batching challenge, whose powers weigh at most
`2 · maxRecursions` claims: `grinding_bits(2 · MAX_RECURSIONS - 1)` (`BATCH_LAM_GRIND_BITS`,
`crates/aggregation/src/deferred.rs`), `2` at `maxRecursions = 16`; at zero bits the batching
neither reads nor absorbs a nonce (`grindProofOfWork`; the guest program's
`const(BATCH_LAM_GRIND_BITS == 0)`). -/
def batchLambdaGrindBits : ℕ := grindingBits (2 * maxRecursions - 1)

/-- The proof of work's nonce in the batching's messages: the nonce, unless the proof of work is of
zero bits (`aggregate_deferred_claims`'s `messages`; `BC_LAM_WORDS`, `lean_ethereum.py`). -/
def lambdaGrindNonceCells (hints : BatchingHints) : List E :=
  if batchLambdaGrindBits = 0 then [] else [hints.lambdaGrindNonce]

/-- A round's cells in the batching's messages: `(g(1), g(∞))`. A round, of degree two, grinds
`grindingBits 2` bits (`absorb_round`), zero at `securityBits = 125`, so it sends no nonce and
`BatchingHints` holds none (`BC_ROUND_WORDS = 2`, `lean_ethereum.py`). Were `grindingBits 2`
nonzero, `sumcheckRoundsProgram` would read a nonce these cells lack: the guest program's
completeness proofs (`lean_vm`) and the comparison of the guest's streams with the Rust's
(`guest-diff`) would fail, until `BatchingHints` carried the rounds' nonces. -/
def sumcheckRoundCells (g : E × E) : List E := [g.1, g.2]

/-- The zeros that pad `wordCount` words to a whole rate. -/
def zerosToWholeRate (wordCount : ℕ) : ℕ := (rateScalars - wordCount % rateScalars) % rateScalars

/-- Words padded with zeros to a whole rate, `rateScalars` words (`pad`,
`crates/aggregation/src/deferred.rs`; `AGG_CHILD_PAD`). -/
def _root_.LeanVM.Node.padToRate (words : List E) : List E :=
  words ++ List.replicate (zerosToWholeRate words.length) 0

/-- **The lambdas of one challenge `λ`**: child `i`'s pair `(λ^(2i), λ^(2i+1))`, for its fresh
claim and its carried one (`lean_ethereum.py`, `crates/aggregation/src/deferred.rs`). -/
def lambdaPowers (challenge : E) (childCount : ℕ) : List (E × E) :=
  (List.range childCount).map fun i ↦ (challenge ^ (2 * i), challenge ^ (2 * i + 1))

/-- The bytecode's batched claim at the lambdas. -/
def batchedClaim (children : List ChildClaims) (lambdas : List (E × E)) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * child.freshClaim.bytecodeValue + l.2 * child.carriedClaim.bytecodeValue) children lambdas)

/-- The bytecode's batched weight at `point`. -/
def batchedBytecodeWeight (children : List ChildClaims) (lambdas : List (E × E))
    (point : List E) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * eqEval child.freshClaim.bytecodePoint point +
      l.2 * eqEval child.carriedClaim.bytecodePoint point) children lambdas)

/-- **The round polynomial** from the claim before the round and its message `(g(1), g(∞))`:
`g(0) = claim + g(1)`, and `g(x) = (g(∞)·x + g(0) + g(1) + g(∞))·x + g(0)`, the degree-2 round
polynomial whose `g(0)` the claim fixes. -/
def sumcheckRoundPolynomial (claim : E) (g : E × E) (x : E) : E :=
  (g.2 * x + ((claim + g.1) + g.1 + g.2)) * x + (claim + g.1)

/-- `roundCount` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, a proof of
work of `grindingBits 2` bits, none at zero (`absorb_round`), sample the challenge, fold
(`sumcheckRoundPolynomial`). The challenges and the final claim. -/
def sumcheckRoundsProgram : (claim : E) → (roundCount : ℕ) → VerifierProgram (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, roundCount + 1 => do
    let g1 ← VerifierProgram.readScalar
    let gInfinity ← VerifierProgram.readScalar
    VerifierProgram.grindProofOfWork (grindingBits 2)
    let challenge ← VerifierProgram.sampleChallenge
    let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInfinity) challenge)
      roundCount
    return (challenge :: rest.1, rest.2)

open Classical in
/-- **The batching after its children**: a proof of work, one challenge and the lambdas of its powers, the
sumcheck's `log₂ |bytecode|` rounds, the final value (`bc_star_hint`, read after the last
challenge: no challenge follows), the final check, and `deferredClaimCheck` of the deferred
claim. -/
noncomputable def batchingAfterChildren (deferredClaimCheck : DeferredBytecodeClaim → Prop)
    (bytecode : List K) (children : List ChildClaims) : VerifierProgram Bool := do
  VerifierProgram.grindProofOfWork batchLambdaGrindBits
  let challenge ← VerifierProgram.sampleChallenge
  let lambdas := lambdaPowers challenge children.length
  let rounds ← sumcheckRoundsProgram (batchedClaim children lambdas) (Nat.log2 bytecode.length)
  let finalValue ← VerifierProgram.readScalar
  VerifierProgram.require (rounds.2 = finalValue * batchedBytecodeWeight children lambdas rounds.1 ∧
    deferredClaimCheck ⟨rounds.1, finalValue⟩)
  return true

/-- The count's cells: the generator's power, padded to a whole rate. -/
def childCountCells (childCount : ℕ) : List E := padToRate [Verifier.gpow childCount]

/-- A child's cells: its words, padded to a whole rate. -/
def childCells (child : ChildClaims) : List E := padToRate child.words

/-- What the batching absorbs before its first challenge. -/
def cellsBeforeChallenge (children : List ChildClaims) : List E :=
  childCountCells children.length ++ children.flatMap childCells

/-- **The batching of a node's children** (`aggregate_claims`): what it absorbs before its first
challenge (`cellsBeforeChallenge`, the count's cells and the children's), read as they are, then the
batching after them, its deferred claim meeting `deferredClaimCheck`. -/
noncomputable def nodeBatchingProgram (deferredClaimCheck : DeferredBytecodeClaim → Prop)
    (bytecode : List K) (children : List ChildClaims) : VerifierProgram Bool := do
  let cells ← VerifierProgram.readScalars (cellsBeforeChallenge children).length
  VerifierProgram.require (cells = cellsBeforeChallenge children)
  batchingAfterChildren deferredClaimCheck bytecode children

/-- **The batching transcript run**, over a permutation `π` in any monad: from the seed
`π(H(label) ‖ 0)`, `H` Keccak-256 over `π` (`FiatShamirState::from_label`; the guest program bakes
its capacity, `AGG_SEED_*`, `crates/aggregation/src/placeholders.rs`), the program on the proof. -/
noncomputable def runBatching {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : VerifierProgram Bool) (proof : Proof) : m Bool := do
  let seed ← π (seedInput (← keccak256With π batchingLabel) (Vector.replicate 4 0))
  runProof π program seed proof

/-- The stream of a node's batching: the count's and the children's cells, the proof of work's
nonce, if it grinds (`lambdaGrindNonceCells`), the sumcheck's messages `(g(1), g(∞))`
(`sumcheckRoundCells`), the final value. -/
def batchingStream (children : List ChildClaims) (hints : BatchingHints) : List E :=
  cellsBeforeChallenge children ++ lambdaGrindNonceCells hints ++
    hints.sumcheckMessages.flatMap sumcheckRoundCells ++ [hints.finalBytecodeValue]

/-! ## The recursion step: the batching in the random-permutation model

The batching program with the count, below a bound, and the children read off the proof's stream
(a node's batching, `nodeBatchingProgram`, knows its children) and the check that the deferred
claim holds of the bytecode (`boundedBatchingProgram`), run on a proof an adversary outputs,
querying `π` and `π⁻¹`; the batching has no statement of its own. -/

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
for the program's query bound `QV = batchingQueryBound bytecode M ≤ 2^96`; the
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
    Common.QueryCostAtMost adversary Common.permutationCallCost QA →
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

end LeanVM.Guest.Batch

end
