module

public import Statement.Prover.Prove
public import Statement.RandomPermutation
public import VCVio.OracleComp.OracleComp
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
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
reads the statement, the proof and the adversary's transcript, and nothing else (it neither queries
`π` nor rewinds the adversary); `Statement.Theorems` states it for the extractor a cost-machine
program of bounded size computes within its budget (`LeanVM.extractorComputedBy`,
`CostMachine.lean`, which gives the bound and the budget). **Completeness** is stated for one honest
prover, `leanVmHonestProver`: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`), an executable
program (`statement.tex` says what a reviewer checks of it).

**Scope and trust**, beyond the model's assumption (`statement.tex`):

* A proof is the Rust verifier's `Proof`: the scalar stream and one full Merkle path per query, with
  its position, grouped in phases. It travels as bytes, its one encoding (`wire.rs`), the paths
  pruned: a compression layer formalized in `lean_vm` (`LeanVM.Wire`, after scaraven's idea and
  formalization, https://github.com/scaraven), where it is proved lossless on honest proofs and the
  only encoding of its proof. That its transcription of `Proof::from_bytes` and `Proof::to_bytes`
  is the Rust's is test evidence (the wire differential).
* That `verifier` is the Rust verifier is test evidence: it accepts the Rust prover's proofs, and
  on mutated proofs it gives the Rust verifier's verdict every time (`scripts/fuzz-verifier.py`).
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

/-! ### The honest prover and the committed size -/

/-- An honest prover: over a permutation `π` in any monad, from a statement, an execution, the
commitment's rate exponent `ρ` and a fuel of nonces per proof of work, a proof, or `none` when it
makes none. -/
abbrev HonestProver : Type 1 :=
  {m : Type → Type} → [Monad m] → (KeccakState → m KeccakState) → (program : LeanIsaProgram) →
    (input : PublicInput) → Execution program → (ρ nonceAttemptsPerProofOfWork : ℕ) →
    m (Option Proof)

/-- **The honest prover**: `LeanVM.Prover.prove` (`Statement/Prover/Prove.lean`). From the
execution it computes the witness (`witness?`, no proof unless the execution is valid and within
`2^28` committed cells), and, at a valid rate, runs the honest script against the verifier's own
program `leanVmVerifierProgram`, trying `nonceAttemptsPerProofOfWork` nonces per proof of work. -/
def leanVmHonestProver : HonestProver :=
  fun π program input execution ρ nonceAttemptsPerProofOfWork ↦
    Prover.prove π program input execution ρ nonceAttemptsPerProofOfWork

/-- **The committed size of an execution**: the number of cells the honest prover commits to, every
committed column at its table's height, the least power of two holding the table's rows (`1` for no
row), and at least `2^9` for the `KECCAK` table (`TABLE_LOG_FLOORS`,
`crates/verifier/src/layout.rs:481`). The memory has three columns of `2^κ` rows (its two limbs and
its final counts), and the bytecode's counts one of `2^logSize` rows (`NUM_GLOBAL_COLUMNS`,
`layout.rs:71-76`, `kappas`, `:525-529`). Each opcode has a table of one row per instruction of
that opcode the execution executes (`Execution.opcodeCount`), with `13, 13, 7, 14, 14, 28`
committed columns for `XOR`, `MUL_NATIVE`, `SET_CONSTANT`, `DEREF`, `JUMP`, `KECCAK`
(`layout.rs:373-378`; of the `KECCAK` table's `92` columns, the `25` input lanes and `14` more ride
`q_keccak`'s slots and the `25` output lanes are not committed, `layout.rs:380-432`); and
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
error every verifier message is held to after its proof of work. The `2^14` covers the verifier's
own Keccak-256 evaluations and duplex permutations, at most `13261` (the `Q + 13261` of `lean_vm`'s
`soundnessError`; as calls of `π` they are up to `13261 · 2^32`, the IV hashing a bytecode of up to
`2^32` instructions, which the transfer below pays), its `13261 · 2^-256` for a fresh hash answer
equal to a stack root the adversary announced without computing it, and the transfer from two
random oracles to one permutation. `Statement.Theorems`
states it for the extractor a cost-machine program computes within its budget
(`LeanVM.extractorComputedBy`, `CostMachine.lean`). The extractor must output some valid execution
of the program on the input; nothing requires it to be the execution the proof commits to (its
committed word). For a program with several valid executions on one input, the one extracted may
differ, and `AggregateSound` (`Corollaries.lean`) then decodes that one. -/
def KnowledgeSoundness (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q → Q ≤ 2 ^ 128 →
    Pr{let outcome ← knowledgeSoundnessExperiment adversary}[
        BreaksKnowledgeSoundness extractor outcome] ≤
      (Q + 2 ^ 14 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 125 +
        5 * (Q + 2 ^ 14 : ℝ≥0∞) ^ 2 * (2 : ℝ≥0∞)⁻¹ ^ 256

/-! ### Completeness -/

/-- **The completeness experiment in the random-permutation model**: the honest prover's proof,
then the verifier's verdict on it, both over `π`, run against the lazily sampled permutation; no
proof is a failure. -/
noncomputable def completenessExperiment (honestProver : HonestProver) (program : LeanIsaProgram)
    (input : PublicInput) (execution : Execution program) (ρ nonceAttemptsPerProofOfWork : ℕ) :
    ProbComp Bool :=
  Common.runWithRandomPermutation do
    match ← honestProver queryPermutation program input execution ρ nonceAttemptsPerProofOfWork with
    | none => pure false
    | some proof => leanVmVerifier queryPermutation program input proof

/-- **Completeness in the random-permutation model**: trying `2^33` nonces per proof of work, the
honest prover's (`leanVmHonestProver`) proof of an execution within the verifier's size cap is
rejected with probability at most `2^-256`. Within that cap the widest grind is the bus's,
`busGrindingBits` of a push tree of depth at most `28`, `25` bits, and `2^33 = 2^25 · 2^8` nonces
miss a `25`-bit proof of work with probability at most `2^-320`. -/
def Completeness : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 28 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment leanVmHonestProver program input execution ρ (2 ^ 33)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
