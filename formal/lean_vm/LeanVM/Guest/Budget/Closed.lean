/-
  LeanVM.Guest.Budget.Closed

  **The guest is complete within the deployed budget**, with no hypothesis left: each child's
  `verify_sub` within `vsBoundAt Count.vsWords vkBound` words at its announced stack log and rate
  (B1-d's `verify_sub_completeBT`, B1-f's `verifySubGoalsTB_of`).
-/

module

public import LeanVM.Guest.Budget.DeployedBudget
public import LeanVM.Guest.Count.VsWords
public import LeanVM.Guest.B1.Main.VerifySubGoals
public import LeanVM.Guest.B1.VerifySub.CompleteBT
public import LeanVM.Guest.B1.KeccakGkr.VkCW
public import LeanVM.Guest.B2C.RunsConsec

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode bytecode_length)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB childBv)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTs vkBound)

@[expose] public section

/-- **Child `c`'s `verify_sub` tree at the deployed instance**: its callees calls of their names
within their bounds at the child's announced stack log and rate (`Budget.FlatShape` for `vsTs`),
the child's candidate among `open_stacked`'s 28. -/
def deployedVsT (w : NodeWitness) (c : ℕ) (t : Tree) : Prop :=
  ∀ hc : c < w.children.length,
    B1.Whir.candidate (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2
      < 28 ∧ FlatShape coreProgram "verify_sub" (vsTs B2C.fs Count.vsWords vkBound
        (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2) t

/-- **Each child's `verify_sub` call at the deployed instance**, within `vsBoundAt Count.vsWords
vkBound` at its announced stack log and rate, by a tree of `deployedVsT`. -/
theorem verifySubGoals_deployed {seed : LeanVM.Protocol.Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w (deployedVsT w)
      (childBv (vsBoundAt Count.vsWords vkBound) w) :=
  B1.Main.verifySubGoalsTB_of bytecode_length B2C.runsFit B2C.runsConsec Count.vsWords
    (B1.VerifySub.verify_keccak_completeAtB_fs 16) hr hok

/-- **The aggregation guest is complete within the deployed budget**: for every seed, statement
and witness with `NodeRelation`, within the deployed limits, the caps agreeing, no zero challenge where
the guest divides, and the node's committed size at the budget at most `2^28`, there is a valid
execution of the guest on the statement's digest within the verifier's size cap; each child's
`verify_sub` charged `vsBoundAt Count.vsWords vkBound` words at its announced stack log and
rate, and `vsCnt op` instructions of each opcode `op` there (`vs_weight_le_deployed`). -/
theorem guest_complete : GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWords vkBound)) :=
  guest_complete_deployed (Pvs := deployedVsT)
    (fun _ _ _ hr _ hok => verifySubGoals_deployed hr hok)
    fun op _ _ hc _ _ _ _ hP hv hb => vs_weight_le_deployed op (hP hc).1 (hP hc).2 hv hb

end
end LeanVM.Guest.Budget
