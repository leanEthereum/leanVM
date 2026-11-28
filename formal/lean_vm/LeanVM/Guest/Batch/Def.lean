/-
  LeanVM.Guest.Batch.Def

  The batching as a program of the verifier's language, on the stream of the children's cells and
  the hints: the form the random-oracle proof runs (`Rom.lean`). `batch`
  (`Statement/LeanVmGuestBatching.lean`) is the batching; `Node.lean` relates the two.
-/

module

public import Statement.LeanVmGuestProver
public import LeanVM.Facts.BytecodeShape

namespace LeanVM.Guest.Batch

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- The batching transcript's initial state (`FiatShamirState::from_label`), as `batch` computes it
over Keccak-f[1600]; the guest program bakes it (`AGG_SEED_*`). -/
def batchSeed : KeccakState := keccakF1600 (seedInput (keccak256 batchingLabel) (Vector.replicate 4 0))

/-- `batch`'s transcript over Keccak-f[1600] from `batchSeed`, without its checks on the children
and the hints (`batch_eq_some_iff`). -/
def batchCore (cs : List ChildClaims) (h : BatchingHints) : Option DeferredBytecodeClaim :=
  Id.run ((batchWith.go (m := Id) keccakF1600 cs h).run' ⟨batchSeed, [], none⟩)

/-- What `batch` checks of the children and the hints, for points of `vars` coordinates. -/
def BatchChecks (vars : ℕ) (cs : List ChildClaims) (h : BatchingHints) : Prop :=
  cs.length ≤ maxRecursions ∧ h.sumcheckMessages.length = vars ∧
    ∀ c ∈ cs, c.freshClaim.bytecodePoint.length = vars ∧ c.carriedClaim.bytecodePoint.length = vars

/-- A child's two claims are at points of `log₂ |bytecode|` coordinates. -/
def ChildHasBytecodeShape (bytecode : List K) (child : ChildClaims) : Prop :=
  child.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length ∧
    child.carriedClaim.bytecodePoint.length = Nat.log2 bytecode.length

/-- The proof of work's nonce in the batching's stream. -/
def lambdaGrindNonceCells (hints : BatchingHints) : List E := [hints.lambdaGrindNonce]

/-- A round's cells in the batching's stream: `(g(1), g(∞))`. -/
def sumcheckRoundCells (g : E × E) : List E := [g.1, g.2]

/-- **`batch` defers a claim exactly where its checks pass and its transcript defers it.** -/
theorem batch_eq_some_iff {vars : ℕ} {cs : List ChildClaims} {h : BatchingHints}
    {d : DeferredBytecodeClaim} : batch vars cs h = some d ↔ BatchChecks vars cs h ∧ batchCore cs h = some d := by
  unfold batch batchWith BatchChecks
  split_ifs with hc
  · exact ⟨fun e ↦ ⟨hc, e⟩, fun e ↦ e.2⟩
  · simp only [hc, false_and, iff_false]
    exact fun e ↦ Option.some_ne_none d e.symm

/-- A node's children, its relation holding, have claims of the bytecode's shape. -/
theorem _root_.LeanVM.Node.NodeRelation.child_shapes {bytecode : List K} {seed : Digest}
    {s : NodeStatement} {w : NodeWitness} (hN : NodeRelation bytecode seed s w) :
    ∀ c ∈ w.children, c.freshClaim.bytecodePoint.length = Nat.log2 bytecode.length ∧
      c.statement.deferredClaim.bytecodePoint.length = Nat.log2 bytecode.length := by
  intro c hc
  have hb := hN.2.2.2
  unfold DeferredClaimBatched at hb
  split_ifs at hb with hw
  · exact absurd hw (List.ne_nil_of_mem hc)
  · exact (batch_eq_some_iff.mp hb).1.2.2 _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

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

end
end LeanVM.Guest.Batch
