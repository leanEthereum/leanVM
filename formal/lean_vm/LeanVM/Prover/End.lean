/-
  LeanVM.Prover.End

  The completeness end theorems, for the statement's honest prover `LeanVM.leanVmHonestProver`
  (`LeanVM.Prover.prove`, `Statement/Prover/Prove.lean`).
-/

import LeanVM.Prover.Assemble
import LeanVM.Prover.Complete
import LeanVM.Protocol.WithHash
import LeanVM.Guest.WithHash
import LeanVM.Guest.ExperimentBridge
import LeanVM.Guest.AcceptableChild

/-!
# The completeness end theorems

`LeanVM.leanVmHonestProver`, the statement's executable honest prover with the oracle calls, is the
specification's honest prover at the execution's witness (`LeanVM.Prover.prove_eq_honestComp`,
from `corr_honestScript`, `LeanVM/Prover/Assemble.lean`; `specOnValid_prove`, `childSpec_prove`), so
the completeness
theorems for such a prover (`completeness_of_spec`, `guestChildComplete_of_spec`,
`LeanVM/Prover/Complete.lean`) prove the end statements:

* `LeanVM.completeness_holds : Completeness`;
* `LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Guest.Child
open OracleComp

section Prove

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-- **The prover with the oracle calls is the specification** at the execution's witness: on a
valid execution within the cap at a valid rate, `proveWithHash callKeccak256 callKeccakF1600` is
`Rom.honestComp?` of the specification's honest strategy at `skelWitness`, its sizes and its
stack. -/
theorem prove_eq_honestComp (hv : ValidExecution prog input t) (hcap : t.committedSize ≤ 2 ^ 28)
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

/-- **The hypothesis of the completeness theorems**: on valid executions within the cap at a
valid rate, the prover is the specification at a child's witness. -/
theorem specOnValid_prove : SpecOnValid oracleProver ChildFor :=
  fun _ _ _ _ fuel hv hcap hρ ↦ ⟨_, _, childFor_trace hv hcap hρ, prove_eq_honestComp hv hcap hρ fuel⟩

/-- The same, at an honest witness. -/
theorem specOnValid_prove_honest : SpecOnValid oracleProver HonestFor :=
  fun prog input t ρ fuel hv hcap hρ ↦
    let ⟨w, s, h, e⟩ := specOnValid_prove prog input t ρ fuel hv hcap hρ
    ⟨w, s, h.1, e⟩

/-- **Everywhere, the prover is the specification at a child's witness or makes no proof.** -/
theorem childSpec_prove (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    ChildSpec oracleProver prog input t ρ fuel := by
  by_cases h : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 28 ∧ 1 ≤ ρ ∧ ρ ≤ 4
  · exact .inr (specOnValid_prove prog input t ρ fuel h.1 h.2.1 h.2.2)
  · left
    show proveWithHash callKeccak256 callKeccakF1600 prog input t ρ fuel = pure none
    unfold proveWithHash
    cases hW : witness? prog input t with
    | none => rfl
    | some W =>
      have hs := (isSome_witness?_iff prog input t).mp (by rw [hW]; rfl)
      have hρ : ¬ (1 ≤ ρ ∧ ρ ≤ 4) := fun hρ ↦ h ⟨hs.1, hs.2, hρ⟩
      simp only [hρ, ↓reduceIte]

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

/-- Both parts of `GuestChildCompleteWithHash`, for the honest prover with the two calls. -/
theorem Guest.Budget.guestChildCompleteWithHash_holds : Guest.Budget.GuestChildCompleteWithHash :=
  guestChildComplete_of_spec LeanVM.proverWithHash specOnValid_prove childSpec_prove

/-- **The honest prover's proofs of guest executions are children the guest accepts**: both parts
of `GuestChildComplete` for `LeanVM.leanVmHonestProver`. -/
theorem Guest.Budget.guest_child_complete : Guest.Completeness.GuestChildComplete :=
  Guest.Budget.guestChildComplete_of_withHash Guest.Budget.guestChildCompleteWithHash_holds

end LeanVM
