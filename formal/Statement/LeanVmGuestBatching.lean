module

public import Statement.LeanVm

/-!
# The leanISA guest program: the batching of the children's claims

The batching program `LeanVmGuest.lean`'s `DeferredClaimBatched` runs, transcribed: the program split
by opcode as one table (`splitTable`), the claim a node defers on it (`DeferredBytecodeClaim`), what a
node knows of each child (`ChildClaims`: its fresh claim, the split columns at its link point, and
its carried claim), and the batching of the children's claims as a program of the verifier's
language (`Batch.nodeBatchingProgram`). Reference material: a first reading takes the program as
the batching of `crates/aggregation/src/deferred.rs` and looks things up here.

Transcribed from leanVM: the modules of
`crates/aggregation/src/` and `guests/lean_ethereum.py`,
cited by their items' names.
-/

@[expose] public section

namespace LeanVM.Node

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

/-! ## The split program (`crates/aggregation/src/split.rs`)

The program split by opcode, as the link reads it: the columns `splitColumns tables` (`split_terms`),
each a function of the instruction `k` (`Column`): `[op_k = op]`, `[op_k = op]·BC_slot(k)` or
`[op_k = op]·g^k·BC_slot(k)`. A child's verification evaluates them at its link point
(`FreshClaim`); a node defers one claim on all of them as one table (`splitTable`). -/

/-- `SPLIT_LOG` (`split.rs`): the split columns pad to `2^splitLog`. -/
def splitLog : ℕ := 6

/-- The variables of a point over the program's instructions, `log₂ n` for the `n = len / 2^BYTECODE_SLOT_BITS`
instructions of the stacked program `bytecode` (`kbc`, `crates/aggregation/src/node.rs`). -/
def instructionVariableCount (bytecode : List K) : ℕ := Nat.log2 (bytecode.length >>> bytecodeSlotBits)

/-- The variables of a deferred claim's point, the instructions' then the split columns'
(`bytecode_vars`, `crates/aggregation/src/deferred.rs`; `BYTECODE_VARS`, `lean_ethereum.py`):
`log₂` of `splitTable`'s length. -/
def deferredVariableCount (bytecode : List K) : ℕ := instructionVariableCount bytecode + splitLog

/-- Entry `k` of split column `j` of the stacked program `bytecode` (`split_table`, `split.rs`): with
`n = len / 2^BYTECODE_SLOT_BITS` instructions, instruction `k`'s slot `s` the word `s·n + k` and its opcode from
slot `3` (`opcodeOf`), `[op_k = op]` (`count`), `[op_k = op]·BC_slot(k)` (`slot`),
`[op_k = op]·g^k·BC_slot(k)` (`pc`, `g^k` in `K`), and `0` for `j` past the split columns. -/
def splitEntry (bytecode : List K) (j k : ℕ) : K :=
  let n := bytecode.length >>> bytecodeSlotBits
  let word := fun s ↦ bytecode.getD (s * n + k) 0
  let op := opcodeOf (word 3)
  match (splitColumns tables)[j]? with
  | some (.count o) => if op = o then 1 else 0
  | some (.slot o slot) => if op = o then word slot else 0
  | some (.pc o slot) => if op = o then g ^ k * word slot else 0
  | none => 0

/-- **The split program as one table** (`split_table`, `split.rs`): column `j` at rows `j·n` to
`(j + 1)·n` for `n` instructions, `2^splitLog` columns, those past the split columns zero. Every
entry is in `K`. A point on it is the instructions' coordinates, then the columns'. -/
def splitTable (bytecode : List K) : List K :=
  (List.range (2 ^ splitLog)).flatMap fun j ↦
    (List.range (bytecode.length >>> bytecodeSlotBits)).map (splitEntry bytecode j)

/-- **The split columns at a point over the instructions** (`split_values`, `split.rs`): the
program's split there (`Bytecode::split`, `splitAt`, at the pairs read times `pc`, `pcSlots`), read
column by column. -/
def splitValues (bytecode : List K) (point : List E) : List E :=
  let split := splitAt bytecode point (pcSlots tables)
  (splitColumns tables).map fun
    | .count op => split.count.getD op 0
    | .slot op slot => (split.slots.getD op []).getD slot 0
    | .pc op slot => (split.pc.getD op []).getD slot 0

/-- **A claim on the split program holds** of the stacked program `bytecode`: its value is the
multilinear extension of `splitTable bytecode` at its point (the value only;
`DeferredBytecodeClaim.HoldsWithShape`, `LeanVmGuest.lean`, adds the power-of-two
length). -/
def _root_.LeanVM.Protocol.Verifier.BytecodeClaim.Holds (bytecode : List K) (claim : BytecodeClaim) :
    Prop :=
  multilinearEval ((splitTable bytecode).map ofK) claim.bytecodePoint = claim.bytecodeValue

/-- **A fresh claim holds** of the stacked program `bytecode`: its values are the split columns at
its point (`FreshClaim::at`, `crates/aggregation/src/deferred.rs`). -/
def _root_.LeanVM.Protocol.Verifier.FreshClaim.Holds (bytecode : List K) (fresh : FreshClaim) : Prop :=
  fresh.values = splitValues bytecode fresh.point

/-- The cells the batching absorbs of a fresh claim: the point, then the values
(`FreshClaim::cells`, `deferred.rs`; `verify_sub`'s `defer_out`, `lean_ethereum.py`). -/
def _root_.LeanVM.Protocol.Verifier.FreshClaim.cells (fresh : FreshClaim) : List E :=
  fresh.point ++ fresh.values

/-! ## The deferred claim -/

/-- The claim a statement defers on the split program: its value at a point
(`DeferredBytecodeClaim`, `crates/aggregation/src/deferred.rs`), the instructions' coordinates then
the split columns'. -/
abbrev DeferredBytecodeClaim : Type := BytecodeClaim

/-- The cells a deferred claim is hashed and absorbed as: the point, then the value
(`DeferredBytecodeClaim::cells`, `crates/aggregation/src/deferred.rs`; the guest program's
`defer_stmt`, `lean_ethereum.py`). -/
def DeferredBytecodeClaim.cells (claim : DeferredBytecodeClaim) : List E :=
  claim.bytecodePoint ++ [claim.bytecodeValue]

/-! ## The batching program

The batching of the children's claims (`aggregate_claims`, `lean_ethereum.py`;
`aggregate_deferred_claims`, `crates/aggregation/src/deferred.rs`), as a program of the verifier's
language (`VerifierProgram`): the cells absorbed before the challenge (`cellsBeforeChallenge`: the
count `n` as `g^n`, then each child's words, each padded with zeros to a whole rate), then a proof of
work of `batchLambdaGrindBits` bits, one challenge `λ`, whose powers are the lambdas, and the
`splitLog` column challenges, which fold each fresh claim's values into one claim on the split table
at its point and the column challenges, the sumcheck's `deferredVariableCount` rounds
(`sumcheckRoundsProgram`) and the final value, accepted if the final claim is the value times the
batched weight and the deferred claim meets a check (`batchingAfterChildren`); run from the batching
transcript's seed (`runBatching`). -/

/-- What a node knows of one child: the child's public input, the claim its verification raises
(`freshClaim`), and the claim its statement defers (`carriedClaim`). -/
structure ChildClaims where
  /-- The child's public input. -/
  publicInput : Digest
  /-- The claim the child's verification raises: the split columns at its link point. -/
  freshClaim : FreshClaim
  /-- The claim the child's statement defers. -/
  carriedClaim : DeferredBytecodeClaim

/-- The words the batching absorbs of a child: its public input's two cells, its fresh claim's
point and values, the claim its statement defers (`aggregate_deferred_claims`'s `words`;
`AGG_CHILD_WORDS`, `lean_ethereum.py`). -/
def ChildClaims.words (child : ChildClaims) : List E :=
  [(digestHalves child.publicInput).1, (digestHalves child.publicInput).2] ++
    child.freshClaim.cells ++ child.carriedClaim.cells

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

/-- The bits of the proof of work before the batching challenges: `λ`'s powers weigh at most
`2 · maxRecursions` claims, and each fresh claim's values are folded at the `splitLog` column
challenges: `grinding_bits(2 · MAX_RECURSIONS - 1 + SPLIT_LOG)` (`BATCH_LAM_GRIND_BITS`,
`crates/aggregation/src/deferred.rs`), `3` at `maxRecursions = 16`; at zero bits the batching
neither reads nor absorbs a nonce (`grindProofOfWork`; the guest program's
`const(BATCH_LAM_GRIND_BITS == 0)`). -/
def batchLambdaGrindBits : ℕ := grindingBits (2 * maxRecursions - 1 + splitLog)

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

/-- `Σ_j eq(column, j)·values[j]`: split columns' values folded at the column challenges `column`
(`fold_columns`, `deferred.rs`), a fresh claim's value on the split table at its point and
`column`. -/
def foldColumns (column values : List E) : E :=
  sumE (List.zipWith (· * ·) (eqKernel column) values)

/-- The split table's batched claim at the lambdas and the column challenges `column`: each
child's fresh claim folded at `column`, and its carried claim. -/
def batchedClaim (children : List ChildClaims) (lambdas : List (E × E)) (column : List E) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * foldColumns column child.freshClaim.values + l.2 * child.carriedClaim.bytecodeValue)
    children lambdas)

/-- The split table's batched weight at `point`: a fresh claim's point is its point over the
instructions, then the column challenges `column`. -/
def batchedBytecodeWeight (children : List ChildClaims) (lambdas : List (E × E))
    (column point : List E) : E :=
  sumE (List.zipWith (fun child l ↦
    l.1 * eqEval (child.freshClaim.point ++ column) point +
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
/-- **The batching after its children**: a proof of work, one challenge and the lambdas of its
powers, the `splitLog` column challenges, the sumcheck's `deferredVariableCount` rounds, the final
value (`bc_star_hint`, read after the last challenge: no challenge follows), the final check, and
`deferredClaimCheck` of the deferred claim. -/
noncomputable def batchingAfterChildren (deferredClaimCheck : DeferredBytecodeClaim → Prop)
    (bytecode : List K) (children : List ChildClaims) : VerifierProgram Bool := do
  VerifierProgram.grindProofOfWork batchLambdaGrindBits
  let challenge ← VerifierProgram.sampleChallenge
  let column ← VerifierProgram.sampleChallenges splitLog
  let lambdas := lambdaPowers challenge children.length
  let rounds ← sumcheckRoundsProgram (batchedClaim children lambdas column)
    (deferredVariableCount bytecode)
  let finalValue ← VerifierProgram.readScalar
  VerifierProgram.require
    (rounds.2 = finalValue * batchedBytecodeWeight children lambdas column rounds.1 ∧
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

end LeanVM.Guest.Batch

end
