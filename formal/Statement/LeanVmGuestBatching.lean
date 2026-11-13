module

public import Statement.LeanVm

/-!
# The leanISA guest program: the batching of the children's claims

The batching program `LeanVmGuest.lean`'s `DeferredClaimBatched` runs, transcribed: the claim a
node defers on the guest program's bytecode (`DeferredClaim`), what a node knows of each child
(`ChildClaims`), and the batching of the children's deferred claims as a program of the verifier's
language (`Batch.nodeBatchingProgram`). Reference material: a first reading takes the program as
the batching of `aggregation/deferred.rs` and looks things up here.

Transcribed from leanVM: the modules of
`crates/rec_aggregation/src/aggregation/` and `crates/rec_aggregation/guests/lean_ethereum.py`;
`aggregation/<module>.rs:N` and `lean_ethereum.py:N` are lines of those files.
-/

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The deferred claim -/

/-- The claim a statement defers on the stacked bytecode: its value at a point (`DeferredClaim`,
`aggregation/deferred.rs:29-32`), the shape of a proof's claim (`BytecodeClaim`). -/
abbrev DeferredClaim : Type := BytecodeClaim

/-- The cells a deferred claim is hashed and absorbed as, and a proof's claim on the bytecode
exported as: the point, then the value (`DeferredClaim::cells`, `aggregation/deferred.rs:84-88`; the
guest program's `defer_stmt`, and `verify_sub`'s `defer_out`, `lean_ethereum.py:3700-3704`). -/
def DeferredClaim.cells (claim : DeferredClaim) : List E :=
  claim.bytecodePoint ++ [claim.bytecodeValue]

/-! ## The batching program

The batching of the children's deferred claims (`aggregate_claims`, `lean_ethereum.py:4854-4964`;
`aggregate_deferred_claims`, `aggregation/deferred.rs:250-357`), as a program of the verifier's
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
  carriedClaim : DeferredClaim

/-- The words the batching absorbs of a child: its public input's two cells, its proof's claim,
the claim its statement defers (`AGG_CHILD_WORDS`, `lean_ethereum.py:387`). -/
def ChildClaims.words (child : ChildClaims) : List E :=
  [(digestHalves child.publicInput).1, (digestHalves child.publicInput).2] ++
    DeferredClaim.cells child.freshClaim ++ child.carriedClaim.cells

/-- The prover's part of a batching: the nonce of the proof of work before the challenge, the
sumcheck's rounds and the bytecode's value at its end (`bc_sumcheck_msgs`, `bc_star_hint`). -/
structure BatchingHints where
  /-- The nonce of the proof of work before the batching challenge. -/
  lambdaGrindNonce : E
  /-- Each round's message `(g(1), g(∞))`. -/
  sumcheckMessages : List (E × E)
  /-- The bytecode's value at the sumcheck's final point. -/
  finalBytecodeValue : E

/-- The batching transcript's label (`RECURSION_AGG_LABEL`, `aggregation/deferred.rs:13`). -/
def batchingLabel : List UInt8 := "leanvm/recursion-aggregation/v1".toUTF8.toList

end LeanVM.Node

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

/-- The bits of the proof of work before the batching challenge, whose powers weigh at most
`2 · MAX_RECURSIONS = 32` claims: `grinding_bits(31) = ⌈log₂ 31⌉ - 3` (`BATCH_LAM_GRIND_BITS`,
`aggregation/deferred.rs:219-220`; `MAX_RECURSIONS`, `aggregation/mod.rs:71`). A round of the
sumcheck, of degree two, grinds `grinding_bits(2) = 0` bits: no proof of work. -/
def batchLambdaGrindBits : ℕ := 2

/-- The zeros that pad `wordCount` words to a whole rate. -/
def zerosToWholeRate (wordCount : ℕ) : ℕ := (rateScalars - wordCount % rateScalars) % rateScalars

/-- Words padded with zeros to a whole rate, `rateScalars` words (`pad`,
`aggregation/deferred.rs:261-265`; `AGG_CHILD_PAD`). -/
def _root_.LeanVM.Node.padToRate (words : List E) : List E :=
  words ++ List.replicate (zerosToWholeRate words.length) 0

/-- **The lambdas of one challenge `λ`**: child `i`'s pair `(λ^(2i), λ^(2i+1))`, for its fresh
claim and its carried one (`lean_ethereum.py:4916-4936`, `aggregation/deferred.rs:281-286`). -/
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

/-- `roundCount` rounds of the batching sumcheck from `claim`: read `g(1)` and `g(∞)`, sample the
challenge, fold (`sumcheckRoundPolynomial`). The challenges and the final claim. -/
def sumcheckRoundsProgram : (claim : E) → (roundCount : ℕ) → VerifierProgram (List E × E)
  | claim, 0 => pure ([], claim)
  | claim, roundCount + 1 => do
    let g1 ← VerifierProgram.readScalar
    let gInfinity ← VerifierProgram.readScalar
    let challenge ← VerifierProgram.sampleChallenge
    let rest ← sumcheckRoundsProgram (sumcheckRoundPolynomial claim (g1, gInfinity) challenge)
      roundCount
    return (challenge :: rest.1, rest.2)

open Classical in
/-- **The batching after its children**: a proof of work, one challenge and the lambdas of its powers, the
sumcheck's `log₂ |bytecode|` rounds, the final value (`bc_star_hint`, read after the last
challenge: no challenge follows), the final check, and `deferredClaimCheck` of the deferred
claim. -/
noncomputable def batchingAfterChildren (deferredClaimCheck : DeferredClaim → Prop)
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
noncomputable def nodeBatchingProgram (deferredClaimCheck : DeferredClaim → Prop)
    (bytecode : List K) (children : List ChildClaims) : VerifierProgram Bool := do
  let cells ← VerifierProgram.readScalars (cellsBeforeChallenge children).length
  VerifierProgram.require (cells = cellsBeforeChallenge children)
  batchingAfterChildren deferredClaimCheck bytecode children

/-- **The batching transcript run**, over a permutation `π` in any monad: from the seed
`π(H(label) ‖ 0)`, `H` Keccak-256 over `π` (`FiatShamirState::from_label`; the guest program bakes
its capacity, `AGG_SEED_*`, `aggregation/placeholders.rs:911-914`), the program on the proof. -/
noncomputable def runBatching {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : VerifierProgram Bool) (proof : Proof) : m Bool := do
  let seed ← π (seedInput (← keccak256With π batchingLabel) (Vector.replicate 4 0))
  runProof π program seed proof

/-- The stream of a node's batching: the count's and the children's cells, the proof of work's
nonce, the sumcheck's messages `(g(1), g(∞))`, the final value. -/
def batchingStream (children : List ChildClaims) (hints : BatchingHints) : List E :=
  cellsBeforeChallenge children ++ [hints.lambdaGrindNonce] ++
    hints.sumcheckMessages.flatMap (fun g ↦ [g.1, g.2]) ++ [hints.finalBytecodeValue]

end LeanVM.Guest.Batch

end
