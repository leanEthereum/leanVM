/-
  LeanVM.Guest.Backend.Guest.Cpl.End

  The guest's completeness through the back end, with no hypothesis, in a cone free of the
  per-function certificates.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Complete
public import LeanVM.Guest.Backend.Complete.FrameWordsDone
public import LeanVM.Guest.Backend.Guest.Cpl.Eval.All

/-!
# The end, certificate free

`guest_complete_backend` at the frame side's words (`Complete.frameWords`) and the evaluated
per-function test (`CplEval.cplOkAll`): `Budget.guest_complete`'s statement with the budget's copy
`deployedBudgetB` (`Link.lean` identifies it with `Budget.deployedBudget`), in a cone that holds
none of the per-function certificate checks.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Budget
open LeanVM.Guest.End (GuestCompleteWithin)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The guest is complete within the deployed budget**, through the back end, no hypothesis. -/
theorem guest_complete_backend_end :
    GuestCompleteWithin (deployedBudgetB (vsBoundAt Count.vsWordsOs vkBound)) :=
  guest_complete_backend Complete.frameWords CplEval.cplOkAll

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_backend_end' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_backend_end
