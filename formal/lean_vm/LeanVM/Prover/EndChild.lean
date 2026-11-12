/-
  LeanVM.Prover.EndChild

  The guest's completeness end theorem, for the statement's honest prover
  `LeanVM.leanVmHonestProver`.
-/

import LeanVM.Prover.End
import LeanVM.Prover.CompleteChild
import LeanVM.Guest.WithHash
import LeanVM.Guest.ExperimentBridge
import LeanVM.Guest.AcceptableChild

/-!
# The guest's completeness end theorem

The statement's honest prover is the specification at a child's witness on every valid execution
within the cap (`specOnValid_prove`), and everywhere that or no proof (`childSpec_prove`), so
`guestChildComplete_of_spec` (`CompleteChild.lean`) proves
`LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete`.
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Guest.Child

section Prove

variable {prog : LeanIsaProgram} {input : PublicInput} {t : Execution prog}

/-- **The hypothesis of the completeness theorems**: on valid executions within the cap at a
valid rate, the prover is the specification at a child's witness. -/
theorem specOnValid_prove : SpecOnValid oracleProver ChildFor :=
  fun _ _ _ _ fuel hv hcap hρ ↦ ⟨_, _, childFor_trace hv hcap hρ, prove_eq_honestComp hv hcap hρ fuel⟩

/-- **Everywhere, the prover is the specification at a child's witness or makes no proof.** -/
theorem childSpec_prove (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    ChildSpec oracleProver prog input t ρ fuel := by
  by_cases h : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 30 ∧ 1 ≤ ρ ∧ ρ ≤ 4
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

/-- Both parts of `GuestChildCompleteWithHash`, for the honest prover with the two calls. -/
theorem Guest.Budget.guestChildCompleteWithHash_holds : Guest.Budget.GuestChildCompleteWithHash :=
  guestChildComplete_of_spec LeanVM.proverWithHash specOnValid_prove childSpec_prove

/-- **The honest prover's proofs of guest executions are children the guest accepts**: both parts
of `GuestChildComplete` for `LeanVM.leanVmHonestProver`. -/
theorem Guest.Budget.guest_child_complete : Guest.Completeness.GuestChildComplete :=
  Guest.Budget.guestChildComplete_of_withHash Guest.Budget.guestChildCompleteWithHash_holds

end LeanVM
