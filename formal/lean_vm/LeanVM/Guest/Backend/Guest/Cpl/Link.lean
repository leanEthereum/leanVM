/-
  LeanVM.Guest.Backend.Guest.Cpl.Link

  The back end's completeness of the guest, stated exactly as `Budget.guest_complete`.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Complete
public import LeanVM.Guest.Budget.DeployedBudget

/-!
# The link to `Budget.guest_complete`'s statement

`guest_complete_backend` is stated with `deployedBudgetB`, a copy of `Budget.deployedBudget`, so
that its cone holds no module of the existing completeness proof. This module, which nothing in
that cone imports, identifies the two budgets and restates the theorem with exactly
`Budget.guest_complete`'s statement.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Budget
open LeanVM.Guest.End (GuestCompleteWithin)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- The copy of the deployed budget is the deployed budget. -/
theorem deployedBudgetB_eq (Bvf : ℕ → ℕ → ℕ) : deployedBudgetB Bvf = deployedBudget Bvf := rfl

/-- **The guest is complete within the deployed budget** (`Budget.guest_complete`'s statement),
through the back end, given the frame side of its completeness and the per-function test of
every entry. -/
theorem guest_complete_link (hFW : Complete.FrameWordsStmt) (hok : CplOkAll) :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) := by
  rw [← deployedBudgetB_eq]
  exact guest_complete_backend hFW hok

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_link
