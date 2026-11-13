/-
  LeanVM.Prover.End

  The completeness end theorem, for the statement's honest prover `LeanVM.leanVmHonestProver`
  (`LeanVM.Prover.prove`, `Statement/Prover/Prove.lean`).
-/

module

public import LeanVM.Prover.Assemble
public import LeanVM.Prover.Complete
public import LeanVM.Protocol.WithHash
public import LeanVM.Protocol.ExperimentBridge

@[expose] public section

/-!
# The completeness end theorem

`LeanVM.leanVmHonestProver`, the statement's executable honest prover with the oracle calls, is the
specification's honest prover at the execution's witness (`prove_eq_honestComp`, from
`corr_honestScript`, `LeanVM/Prover/Assemble.lean`), so the completeness theorem for such a prover
(`completeness_of_spec`, `LeanVM/Prover/Complete.lean`) proves the end statement
`LeanVM.completeness_holds : Completeness`. The guest's, `GuestChildComplete`, is in
`EndChild.lean`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete
open OracleComp

section Prove

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-- **The prover with the oracle calls is the specification** at the execution's witness: on a
valid execution within the cap at a valid rate, `proveWithHash callKeccak256 callKeccakF1600` is
`Rom.honestComp?` of the specification's honest strategy at `skelWitness`, its sizes and its
stack. -/
theorem prove_eq_honestComp (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 30)
    {ρ : ℕ} (hρ : 1 ≤ ρ ∧ ρ ≤ 4) (fuel : ℕ) :
    proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel =
      Rom.honestComp? (leanVmSeed (bytecodeWords prog) (publicInputDigest input))
        (leanVmVerifierProgram (bytecodeWords prog) (publicInputDigest input))
        (leanVmProver prog (traceSizes prog input t) ρ
          (stackOf prog (traceSizes prog input t) (traceWitness prog input t))) fuel := by
  obtain ⟨W, hW, hspec⟩ := witness?_spec hv hcap
  simp only [proveWithHash, hW, hρ, and_self, ↓reduceIte, Rom.honestComp?,
    seedRun_leanVmSeed]
  refine congrArg (fun k : KeccakState → OracleComp KeccakCalls (Option Proof) ↦
    seedWithHash callKeccak256 callKeccakF1600 (bytecodeWords prog) (publicInputDigest input) >>= k)
    (funext fun seed ↦ ?_)
  rw [runScript_corr callKeccak256 callKeccakF1600 fuel _ (corr_honestScript hv hcap hρ hspec) seed,
    runScript_eq_proveM]
  rfl

/-- The statement's honest prover is `prove` with the oracle calls. -/
abbrev oracleProver : HonestProverWithHash := LeanVM.proverWithHash

/-- **The hypothesis of the completeness theorem**: on valid executions within the cap at a
valid rate, the prover is the specification at an honest witness. -/
theorem specOnValid_prove_honest : SpecOnValid oracleProver HonestFor :=
  fun _ _ _ _ fuel hv hcap hρ ↦
    ⟨_, _, (childFor_trace hv hcap hρ).1, prove_eq_honestComp hv hcap hρ fuel⟩

end Prove

end LeanVM.Prover

namespace LeanVM

open LeanVM.Prover

/-- Completeness in the experiment with the two calls, for the honest prover with them. -/
theorem completenessWithHash_holds : CompletenessWithHash :=
  completeness_of_spec LeanVM.proverWithHash specOnValid_prove_honest

/-- **Completeness holds** (in the random-permutation model), for the honest prover
`LeanVM.leanVmHonestProver`: its experiment is the one with the two calls
(`completeness_of_withHash`). -/
theorem completeness_holds : Completeness :=
  completeness_of_withHash completenessWithHash_holds

end LeanVM

end
