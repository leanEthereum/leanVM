/-
  LeanVM.Guest.Budget.Closed

  **The guest is complete within the deployed budget**: each child's `verify_sub` within
  `vsBoundAt Count.vsWordsOs vkBound` words at its announced stack log and rate, through the back
  end's completeness (`Cpl.guest_complete_backend`).
-/

module

public import LeanVM.Guest.Compiled.Cpl.Complete
public import LeanVM.Compiler.Complete.FrameWordsDone
public import LeanVM.Guest.Compiled.Cpl.Eval.All

namespace LeanVM.Guest.Budget

open LeanVM.Guest
open LeanVM.Guest.End (GuestCompleteWithin)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The aggregation guest is complete within the deployed budget**: for
every seed, statement and witness with `NodeRelation`, within the deployed limits, the caps
agreeing, no zero challenge where the guest divides, and the node's committed size at the budget
at most `2^30`, there is a valid execution of the guest on the statement's digest within the
verifier's size cap; each child's `verify_sub` charged `vsBoundAt Count.vsWordsOs vkBound` words
at its announced stack log and rate, and `vsCnt op` instructions of each opcode `op` there
(`vs_weight_le_deployed`). The back end's completeness at its own cells (`Cpl.certG`), from the
frame side's words (`Complete.frameWords`) and the per-function test of every entry
(`CplEval.cplOkAll`). -/
theorem guest_complete :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  Compiled.Cpl.guest_complete_backend Compiler.Complete.frameWords Compiled.CplEval.cplOkAll

end
end LeanVM.Guest.Budget

/-- info: 'LeanVM.Guest.Budget.guest_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.guest_complete
