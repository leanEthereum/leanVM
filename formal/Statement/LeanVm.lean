module

public import Statement.Prover.Prove
public import Statement.RandomPermutation
public import VCVio.EvalDist.ProbabilityNotation

/-!
# leanVM: knowledge soundness and completeness

A statement (a program and a public input), the verifier on it, and the end statements in the
random-permutation model (`RandomPermutation.lean`; `statement.tex`, *The setting*),
`LeanVM.KnowledgeSoundness` and `LeanVM.Completeness`, proved by `LeanVM.knowledgeSoundness_holds`
and `completeness_holds` (`statement.tex` says how they reach this model).

The verifier (`leanVmVerifier π`) and the honest prover are written over a permutation `π` in any
monad, Keccak-256 the sponge over `π` (`keccak256With π`); in the model `π` is
`Common.queryPermutation`, and with Keccak-f[1600] in `Id` they are the deployed ones. The
adversary (`RandomPermutationAdversary`) flips private coins and queries `π` and `π⁻¹`, every query
and its answer recorded in order (`Common.loggedOracles`, `Common.OracleQueryLog`), its coins not
counted (`Common.permutationCallCost`); a Keccak-256 evaluation is a sequence of forward queries,
which it makes itself. The experiment (`knowledgeSoundnessExperiment`) is one game: the adversary,
then the verifier on its statement and proof, run against the lazily sampled permutation from no
edge (`Common.runWithRandomPermutation`).

**Knowledge soundness** is stated for a straight-line extractor (`StraightLineExtractor`), which
reads the statement, the proof and the adversary's transcript, and nothing else;
`Statement.Theorems` states it for the extractor a cost-machine program computes
(`LeanVM.extractorComputedBy`, `CostMachine.lean`). **Completeness** is stated for one honest
prover, `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`). A proof is the Rust verifier's
`Proof`; its wire encoding is a compression layer, formalized in `lean_vm` (`statement.tex`).
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Common
  (RandomPermutationOracles OracleQueryLog PermutationQuery PermutationEdges queryPermutation)
open scoped ENNReal

/-! ### The verifier on a statement -/

-- The bytecode the verifier reads (`bytecodeWords`) and the public input as it reads it
-- (`publicInputDigest`) are `LeanIsa.lean`'s, where the encoding is.

/-- **The leanVM verifier** over a permutation `π` in any monad `m`, Keccak-256 the sponge over
`π`: does `proof` show that `program` runs on `input`? -/
def leanVmVerifier {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool :=
  verifyWith π (bytecodeWords program) (publicInputDigest input) proof

/-- A statement: a program and a public input. -/
abbrev ProgramAndInput : Type := LeanIsaProgram × PublicInput

/-! ### The committed size -/

/-- **The committed size of an execution**: the number of cells the honest prover commits to, every
committed column at its table's height, the least power of two holding the table's rows (`1` for no
row), and at least `2^9` for the `KECCAK` table (`TABLE_LOG_FLOORS`,
`crates/verifier/src/layout.rs`). The memory has three columns of `2^κ` rows (its two limbs and
its final counts), and the bytecode's counts one of `2^logSize` rows (`NUM_GLOBAL_COLUMNS`,
`layout.rs`, `kappas`). Each opcode has a table of one row per instruction of
that opcode the execution executes (`Execution.opcodeCount`), with `13, 13, 7, 14, 14, 28`
committed columns for `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK`
(`layout.rs`; of the `KECCAK` table's `92` columns, the `25` input lanes and `14` more ride
`q_keccak`'s slots and the `25` output lanes are not committed, `layout.rs`); and
`q_keccak` has `2^6` rows per row of the `KECCAK` table. -/
noncomputable def Semantics.Execution.committedSize {program : LeanIsaProgram}
    (execution : Execution program) : ℕ :=
  let height (op : Opcode) : ℕ := 2 ^ Nat.clog 2 (execution.opcodeCount op)
  let keccakHeight : ℕ := 2 ^ max (Nat.clog 2 (execution.opcodeCount .keccak)) 9
  3 * 2 ^ execution.logMemorySize + 2 ^ program.logSize +
    13 * height .xor + 13 * height .mulNative + 7 * height .setConstant + 14 * height .deref +
    14 * height .jump + 28 * keccakHeight + 2 ^ 6 * keccakHeight

/-! ### The experiment -/

/-- An adversary in the random-permutation model: a computation with private coins and oracle
access to `π` and `π⁻¹` that outputs a statement and a proof. -/
abbrev RandomPermutationAdversary : Type :=
  OracleComp RandomPermutationOracles (ProgramAndInput × Proof)

/-- **An outcome of the experiment**: the statement and proof the adversary outputs, the
verifier's verdict, and the adversary's transcript. -/
structure ExperimentOutcome where
  /-- The adversary's program. -/
  program : LeanIsaProgram
  /-- Its public input. -/
  input : PublicInput
  /-- Its proof. -/
  proof : Proof
  /-- The verifier accepted the proof. -/
  accepted : Bool
  /-- The adversary's queries and their answers, in order. -/
  transcript : OracleQueryLog

/-- **The random-permutation experiment**: the adversary, its queries recorded
(`Common.loggedOracles`), then the verifier over `π` (`Common.queryPermutation`) on its statement
and proof, the whole game run against the lazily sampled permutation from no edge
(`Common.runWithRandomPermutation`). -/
noncomputable def knowledgeSoundnessExperiment (adversary : RandomPermutationAdversary) :
    ProbComp ExperimentOutcome :=
  Common.runWithRandomPermutation do
    let (((program, input), proof), transcript) ← (simulateQ Common.loggedOracles adversary).run []
    let accepted ← leanVmVerifier queryPermutation program input proof
    return ⟨program, input, proof, accepted, transcript⟩

/-! ### The extractor -/

/-- The permutation queries of a transcript and their answers, oldest first: its coins left out. -/
def permutationQueries (transcript : OracleQueryLog) : List
    (PermutationQuery KeccakState × KeccakState) :=
  transcript.filterMap fun
    | ⟨.inl _, _⟩ => none
    | ⟨.inr q, y⟩ => some (q, y)

/-- **A straight-line extractor**: from the statement (a program and a public input), the
adversary's transcript and the proof, an execution of the program, or none. It reads nothing
else: it neither queries `π` nor runs the adversary again. -/
abbrev StraightLineExtractor : Type :=
  (program : LeanIsaProgram) → PublicInput → OracleQueryLog → Proof → Option (Execution program)

/-! ### Knowledge soundness -/

/-- **The adversary breaks soundness** for the extractor `extractor`: the verifier accepts its
statement and proof, and the execution `extractor` extracts from the transcript and the proof is
not a valid execution of the program on the public input (no execution, `none`, is a break). -/
def BreaksKnowledgeSoundness (extractor : StraightLineExtractor) (outcome : ExperimentOutcome) :
    Prop :=
  outcome.accepted ∧ ¬ ∃ execution,
    extractor outcome.program outcome.input outcome.transcript outcome.proof = some execution ∧
      ValidExecution outcome.program outcome.input execution

/-- **Knowledge soundness in the random-permutation model**, for the extractor `extractor`: an
adversary of at most `Q ≤ 2^128` queries to `π` and `π⁻¹` (its coins free) breaks soundness with
probability at most `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`, `2^-125` the round-by-round
error of every verifier message after its proof of work; `statement.tex` accounts for `2^14`. The
extractor must output some valid execution of the program on the input, not necessarily the one
the proof commits to. -/
def KnowledgeSoundness (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[
        BreaksKnowledgeSoundness extractor outcome] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof
(`LeanVM.Prover.prove`, `Statement/Prover/Prove.lean`, at the rate exponent `ρ`, trying
`nonceAttemptsPerProofOfWork` nonces per proof of work), then the verifier's verdict on it, both
over `π`, run against the lazily sampled permutation; no proof is a failure. -/
noncomputable def completenessExperiment (program : LeanIsaProgram) (input : PublicInput)
    (execution : Execution program) (ρ nonceAttemptsPerProofOfWork : ℕ) : ProbComp Bool :=
  Common.runWithRandomPermutation do
    match ← Prover.prove queryPermutation program input execution ρ
        nonceAttemptsPerProofOfWork with
    | none => pure false
    | some proof => leanVmVerifier queryPermutation program input proof

/-- **Completeness in the random-permutation model**: trying `2^35` nonces per proof of work, the
honest prover's (`LeanVM.Prover.prove`) proof of an execution within the verifier's size cap is
rejected with probability at most `2^-256`. Within that cap the widest grind is the bus's,
`busGrindingBits` of a push tree of depth at most `30`, `27` bits, and `2^35 = 2^27 · 2^8` nonces
miss a `27`-bit proof of work with probability at most `2^-320`. -/
def Completeness : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment program input execution ρ (2 ^ 35)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
