module

public import Statement.Prover.Prove
public import Statement.Prover.Execute
public import Statement.RandomPermutation
public import VCVio.EvalDist.ProbabilityNotation

/-!
# leanVM: knowledge soundness and completeness

A statement (a program and a public input), the verifier on it, and the end statements in the
random-permutation model (`RandomPermutation.lean`; `statement.tex`, *The setting*),
`LeanVM.KnowledgeSoundness` and `LeanVM.Completeness` (`Statement.Theorems`).

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
`Statement.Theorems` states it for the extractor a cost-machine program
computes (`LeanVM.extractorComputedBy`, `CostMachine.lean`). **Completeness** is stated for one honest
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

/-- The table rows of an execution, in opcode order (`table_rows`, the sizes the proof announces):
one row per instruction of the table's opcode the execution executes (`Execution.opcodeCount`). -/
noncomputable def Semantics.Execution.tableRows {program : LeanIsaProgram}
    (execution : Execution program) : List ℕ :=
  [Opcode.xor, .mulNative, .setConstant, .deref, .jump, .keccak].map execution.opcodeCount

/-- Each table's log-height: the least `h` with `rows ≤ 2^h`, at least its floor
(`TABLE_LOG_FLOORS`: `KECCAK`'s block of steps), as `buildLayout` (`build_layout`, `layout.rs`)
computes it. -/
noncomputable def Semantics.Execution.tableLogHeights {program : LeanIsaProgram}
    (execution : Execution program) : List ℕ :=
  List.zipWith (fun rows floor ↦ max (log2Ceil rows) floor) execution.tableRows tableLogFloors

/-- **The committed size of an execution**: the words the stack holds before its padding to a power
of two, every block of the stack (`stackBlocks`, `stack_blocks`, `layout.rs`) at its column's
log-size (`columnKappas`, `column_kappas`), the total `stackOffsets` (`stack_offsets`,
`multilinear.rs`) lays them out in: the memory's two columns of `2^κ` words, `q_keccak` of
`2^slot_bits` words per row of the `KECCAK` table, and every other committed table column at its
table's height; the program commits no column. The stack's log-size is
`max(⌈log₂ committedSize⌉, MIN_STACKED_LOG)`, so `committedSize ≤ 2^30` is exactly the prover's
`MAX_STACKED_LOG` cap. -/
noncomputable def Semantics.Execution.committedSize {program : LeanIsaProgram}
    (execution : Execution program) : ℕ :=
  let kappas := columnKappas tables execution.logMemorySize execution.tableLogHeights
  (stackBlocks.map fun b ↦ 2 ^ kappas.getD b.column 0).sum

/-- **The pointer width of an execution**: `pointer_width(log_memory, log_bytecode, cycles)`
(`link.rs`), the cycles its tables' rows in all (`verify_link`); the link proves its pointers in
this many bits, at most `MAX_WIDTH = maxPointerWidth = 24` (`Chunks::new`). -/
noncomputable def Semantics.Execution.pointerWidth {program : LeanIsaProgram}
    (execution : Execution program) : ℕ :=
  Protocol.Verifier.pointerWidth execution.logMemorySize program.logSize execution.tableRows.sum

/-- `cells` words from the memory address `address` lie in one window of `keccakWindow = 16` words
(`KECCAK_WINDOW`, `crates/isa/src/lib.rs`): its index `i` (`address = g^i`) has
`i % 16 + cells ≤ 16`. -/
def Semantics.InKeccakWindow (κ : ℕ) (address : K) (cells : ℕ) : Prop :=
  ∀ i ∈ addressIndex? κ address, i.val % Prover.Exec.keccakWindow + cells ≤ Prover.Exec.keccakWindow

/-- A `KECCAK` at the frame `fp` has its blocks each in one window (`Op::Keccak`, `execute.rs`,
which faults with `Fault::KeccakAcrossWindow` otherwise): its `tail` (input cells `4` to `7`), its
`cap` (input cells `9` to `12`) and the output cells it writes; any other instruction, trivially. -/
def Semantics.KeccakBlocksInWindowsAt (κ : ℕ) (fp : K) : LeanIsaInstruction → Prop
  | .keccak _ otail _ ocap oout _ _ outCells =>
    InKeccakWindow κ (fp * otail) 4 ∧ InKeccakWindow κ (fp * ocap) 4 ∧
      InKeccakWindow κ (fp * oout) outCells.cellCount
  | _ => True

/-- Every `KECCAK` executed in `n` steps from `r`, stepping as `run` does (as `opcodeCountInRun`
counts them), has its blocks each in one window. -/
noncomputable def Semantics.keccakBlocksInWindowsInRun {κ : ℕ} (program : LeanIsaProgram)
    (memory : MemoryImage κ) : ℕ → Registers K → Prop
  | 0, _ => True
  | n + 1, r =>
    match program.fetch r.pc, step program memory r with
    | some ins, some r' =>
      KeccakBlocksInWindowsAt κ r.fp ins ∧ keccakBlocksInWindowsInRun program memory n r'
    | _, _ => True

/-- **Every `KECCAK` of the execution has its blocks in windows**: the Rust executor faults on any
other (`Fault::KeccakAcrossWindow`), and the link reads a block through one window
(`isa::KECCAK_WINDOW`). -/
def Semantics.Execution.KeccakBlocksInWindows {program : LeanIsaProgram}
    (execution : Execution program) : Prop :=
  keccakBlocksInWindowsInRun program execution.memory execution.stepCount Registers.initial

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
adversary of at most `Q` queries to `π` and `π⁻¹` (its coins free) breaks soundness with
probability at most `(Q + 2^14) · 2^-125 + 5 (Q + 2^14)² · 2^-256`, `2^-125` the round-by-round
error of every verifier message after its proof of work; `statement.tex` accounts for `2^14`. The
extractor must output some valid execution of the program on the input, not necessarily the one
the proof commits to. -/
def KnowledgeSoundness (extractor : StraightLineExtractor) : Prop :=
  ∀ (adversary : RandomPermutationAdversary) (Q : ℕ),
    Common.QueryCostAtMost adversary Common.permutationCallCost Q →
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
honest prover's (`LeanVM.Prover.prove`) proof of an execution within the verifier's size cap
(`committedSize ≤ 2^30`), whose pointers fit the link's width (`pointerWidth ≤ maxPointerWidth`,
`MAX_WIDTH`) and whose `KECCAK`s have their blocks in windows (`KeccakBlocksInWindows`), is rejected
with probability at most `2^-256`. -/
def Completeness : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 →
    execution.pointerWidth ≤ maxPointerWidth → execution.KeccakBlocksInWindows → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment program input execution ρ (2 ^ 35)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
