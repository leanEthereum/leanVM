/-
  LeanVM.Guest.Backend.Guest.Cpl.Link

  The back end's completeness of the guest, stated exactly as `Budget.guest_complete`.
-/

module

public import LeanVM.Guest.Backend.Guest.Cpl.Complete
public import LeanVM.Guest.Budget.DeployedBudget
public import LeanVM.Guest.Backend.Complete.FrameWordsDone
public import LeanVM.Guest.Backend.Guest.Cpl.Eval.All

/-!
# The link to `Budget.guest_complete`'s statement

`guest_complete_link` is `guest_complete_backend` under its name in this module; the theorems
below reduce its hypotheses.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Guest LeanVM.Guest.Budget
open LeanVM.Guest.End (GuestCompleteWithin)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The guest is complete within the deployed budget** (`Budget.guest_complete`'s statement),
through the back end, given the frame side of its completeness and the per-function test of
every entry. -/
theorem guest_complete_link (hFW : Complete.FrameWordsStmt) (hok : CplOkAll) :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  guest_complete_backend hFW hok

/-- **The guest is complete within the deployed budget**, the frame side reduced to its chains of
`match`es (`ChainBody`), given the per-function test. -/
theorem guest_complete_of_frame (hch : Complete.ChainBody) (hok : CplOkAll) :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  guest_complete_link (Complete.frameWords_of_fa_chain Complete.faBody Complete.aFaBody hch) hok

/-- **The frame of every instance is consistent** (`FrameConsistentStmt`), from the frame side's
words (`frameWords`) and the run side (`pathRunStmt`). -/
theorem frameConsistentStmt : Complete.FrameConsistentStmt :=
  Complete.frameConsistent_of_words Complete.frameWords

/-- **The guest is complete within the deployed budget**, exactly `Budget.guest_complete`'s
statement, through the back end: no hypothesis. -/
theorem guest_complete_cpl :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  guest_complete_link Complete.frameWords CplEval.cplOkAll

end
end LeanVM.Guest.Backend.Cpl

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_link' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_link

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_of_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_of_frame

/-- info: 'LeanVM.Guest.Backend.Cpl.frameConsistentStmt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.frameConsistentStmt

/-- info: 'LeanVM.Guest.Backend.Cpl.guest_complete_cpl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Backend.Cpl.guest_complete_cpl
