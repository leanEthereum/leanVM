/-
  LeanVM.Prover.EndChild

  The statement's honest prover `LeanVM.Prover.prove` makes children the guest accepts
  (`GuestChildComplete`), a step of the honest-children remark.
-/

module

public import LeanVM.Prover.End
public import LeanVM.Guest.Child.Deployed
public import LeanVM.Guest.WithHash
public import LeanVM.Guest.ExperimentBridge
public import LeanVM.Guest.AcceptableChild

@[expose] public section

/-!
# The honest prover's children

The statement's honest prover is the specification at a child's witness on every valid execution
within the cap, at a valid rate, and makes no proof elsewhere (`childSpec_prove`), so
`Child.childOk_of_spec` (`LeanVM/Guest/Child/Deployed.lean`) proves
`LeanVM.Guest.Budget.guest_child_complete : GuestChildComplete`. Where the verifier accepts the
honest proof, the deferring verifier accepts it with exactly one claim, a true one
(`LeanVM.verifyDeferred_of_leanVmVerifier`), so a child carrying it that `NodeRelation` admits has
a true fresh claim (`Completeness.freshClaim_holds_of_leanVmVerifier`, `Guest/HonestChildren.lean`).
-/

namespace LeanVM.Prover

open LeanVM.Parameters LeanVM.Semantics LeanVM.Arithmetization LeanVM.Protocol
open LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Protocol.LeanIsa
open LeanVM.Protocol.EndToEnd.Front LeanVM.Protocol.EndToEnd.Complete LeanVM.Guest.Child

section Prove

/-- **Everywhere, the prover is the specification at a child's witness or makes no proof.** -/
theorem childSpec_prove (prog : LeanIsaProgram) (input : PublicInput) (t : Execution prog) (ρ
    fuel : ℕ) :
    ChildSpec oracleProver prog input t ρ fuel := by
  by_cases h : ValidExecution prog input t ∧ t.committedSize ≤ 2 ^ 30 ∧ 1 ≤ ρ ∧ ρ ≤ 4
  · exact .inr ⟨_, _, childFor_trace h.1 h.2.1 h.2.2, prove_eq_honestComp h.1 h.2.1 h.2.2 fuel⟩
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

/-- **The honest prover's proofs of guest executions are children the guest accepts**:
`GuestChildComplete` for `LeanVM.Prover.prove`. -/
theorem Guest.Budget.guest_child_complete : Guest.Completeness.GuestChildComplete := by
  intro child hHonest hShape hVerifies
  obtain ⟨hHolds, execution, ρ, hSome⟩ := hHonest
  rw [Guest.Budget.honestProofWithDeployedKeccak_eq_withHash] at hSome
  exact Guest.Child.childOk_of_spec (childSpec_prove _ _ execution ρ _) hShape hHolds hSome hVerifies

end LeanVM

end
