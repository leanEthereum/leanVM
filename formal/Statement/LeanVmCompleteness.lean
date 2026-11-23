module

public import Statement.LeanVm
public import Statement.Prover.Prove

/-!
# leanVM: completeness

The honest prover (`leanVmHonestProver`, the executable `LeanVM.Prover.prove` of
`Statement/Prover/Prove.lean`; `statement.tex` says what a reviewer checks of it), the committed
size of an execution, and the end statement `LeanVM.Completeness` in the random-permutation model,
proved by `completeness_holds`. The prover is written over a permutation `π` in any monad, as the
verifier is (`LeanVm.lean`).
-/

@[expose] public section

namespace LeanVM

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.KeccakHash
open OracleComp OracleSpec
open Common (queryPermutation)
open scoped ENNReal

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
`2^30` committed cells), and, at a valid rate, runs the honest script against the verifier's own
program `leanVmVerifierProgram`, trying `nonceAttemptsPerProofOfWork` nonces per proof of work. -/
def leanVmHonestProver : HonestProver :=
  fun π program input execution ρ nonceAttemptsPerProofOfWork ↦
    Prover.prove π program input execution ρ nonceAttemptsPerProofOfWork

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

/-- **Completeness in the random-permutation model**: trying `2^35` nonces per proof of work, the
honest prover's (`leanVmHonestProver`) proof of an execution within the verifier's size cap is
rejected with probability at most `2^-256`. Within that cap the widest grind is the bus's,
`busGrindingBits` of a push tree of depth at most `30`, `27` bits, and `2^35 = 2^27 · 2^8` nonces
miss a `27`-bit proof of work with probability at most `2^-320`. -/
def Completeness : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 → 1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let v ← completenessExperiment leanVmHonestProver program input execution ρ (2 ^ 35)}[
        v = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 256

end LeanVM

end
