/-
  LeanVM.Guest.RefusingZero

  The leanVM verifier refusing every zero challenge, and the honest proof rarely refused by it: the
  end statement's earlier hypothesis on honest children, now a `lean_vm` result.
-/

module

public import Statement.LeanVmGuestCompleteness

/-!
# The verifier refusing a zero challenge

The guest program completes on a zero challenge, so the end statements no longer name a verifier
refusing one. `lean_vm` keeps it for the guest's completeness on honest children
(`EndExec.guestExecution_complete_on_honest_children`, through `HonestChild`) and proves the honest
proof rarely refused by it (`HonestProofRarelyRefused`, `Completeness.honest_proof_rarely_refused`).
-/

@[expose] public section

open scoped ENNReal

namespace LeanVM.Guest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

namespace Completeness

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

/-- **The leanVM verifier refusing every zero challenge** (`VerifierProgram.refusingZeroChallenge`),
the check `HonestProofRarelyRefused` bounds. -/
def verifierRefusingZero {m : Type → Type} [Monad m] (π : KeccakState → m KeccakState)
    (program : LeanIsaProgram) (input : PublicInput) (proof : Proof) : m Bool := do
  let seed ← spongeSeedWith π (bytecodeWords program) (publicInputDigest input)
  runProof π
    (do
      verifyExecution computedBytecodeValue (bytecodeWords program) (publicInputDigest input)
      return true : VerifierProgram Bool).refusingZeroChallenge
    seed proof

open OracleComp OracleSpec in
/-- **The honest proof is rarely refused**: in the random-permutation model, at `2^35` nonces per
proof of work, the honest prover `LeanVM.leanVmHonestProver` (`LeanVm.lean`, `LeanVM.Prover.prove`)
makes no proof, or `verifierRefusingZero` rejects its proof, of a valid execution of committed size
at most `2^30`, at an inverse rate `2^ρ`, `1 ≤ ρ ≤ 4`, with probability at most `2^-100`. -/
def HonestProofRarelyRefused : Prop :=
  ∀ (program : LeanIsaProgram) (input : PublicInput) (execution : Execution program) (ρ : ℕ),
    ValidExecution program input execution → execution.committedSize ≤ 2 ^ 30 →
    1 ≤ ρ ∧ ρ ≤ 4 →
    Pr{let accepted ← Common.runWithRandomPermutation (do
        match ← LeanVM.leanVmHonestProver Common.queryPermutation program input execution ρ (2 ^
            35) with
        | none => pure false
        | some proof =>
          verifierRefusingZero Common.queryPermutation program input proof)}[accepted = false] ≤
      (2 : ℝ≥0∞)⁻¹ ^ 100

end Completeness

end LeanVM.Guest

end
