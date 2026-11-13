/-
  LeanVM.Guest.Budget.Closed

  **The guest is complete within the deployed budget**: each child's `verify_sub` within
  `vsBoundAt Count.vsWordsOs vkBound` words at its announced stack log and rate
  (`vsCompleteHyp_fs`, `verifySubGoalsTB_of`).
-/

module

public import LeanVM.Guest.Budget.DeployedBudget
public import LeanVM.Guest.Count.VsWordsOs
public import LeanVM.Guest.B1.Main.VerifySubGoals
public import LeanVM.Guest.B1.VerifySub.CompleteHyp
public import LeanVM.Guest.B2C.RunsConsec

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode bytecode_length)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB childBv)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTsAny vkBound)

@[expose] public section

/-- **Child `c`'s `verify_sub` tree at the deployed instance**: its stack log among
`open_stacked`'s arms, `20` to `30`, its callees calls of their names within their bounds at the
child's announced stack log and rate (`vsTsAny`). -/
def deployedVsT (w : NodeWitness) (c : ℕ) (t : Tree) : Prop :=
  ∀ hc : c < w.children.length,
    (childShape bytecode w.children[c]).1 - B1.Whir.minOpenLog < B1.Whir.openArms ∧
      (20 ≤ (childShape bytecode w.children[c]).1 ∧ (childShape bytecode w.children[c]).1 ≤ 30 ∧
        vsTsAny B2C.fs Count.vsWordsOs vkBound (childShape bytecode w.children[c]).1
          (childShape bytecode w.children[c]).2 t)

/-- **`verify_sub`'s completeness at the deployed instance**, in `VerifySubGoals`' form
(`vsCompleteHyp_fs`), its tree also at a stack log in `[20, 30]` (`VsCompleteHyp.shape`). -/
theorem vsCompleteHyp_deployed :
    B1.Main.VsCompleteHyp bytecode B2C.fs B2C.cert 16
      (fun μ r t => 20 ≤ μ ∧ μ ≤ 30 ∧ vsTsAny B2C.fs Count.vsWordsOs vkBound μ r t)
      (vsBoundAt Count.vsWordsOs vkBound) :=
  let h := B1.VerifySub.vsCompleteHyp_fs bytecode_length B2C.runsFit B2C.runsConsec Count.vsWordsOs
  { complete := fun seed c sqE outE Lin hok hexp hout =>
      (h.complete seed c sqE outE Lin hok hexp hout).mono le_rfl
        fun _ ht => ⟨(h.shape seed c hok).1, (h.shape seed c hok).2.1, ht⟩
    shape := h.shape }

/-- **Each child's `verify_sub` call at the deployed instance**, within `vsBoundAt
Count.vsWordsOs vkBound` at its announced stack log and rate, by a tree of `deployedVsT`. -/
theorem verifySubGoals_deployed {seed : LeanVM.Protocol.Digest}
    {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRelation bytecode seed s w) (hok : ChildrenOk bytecode seed w) :
    VerifySubGoalsTB B2C.fs B2C.cert 0 seed s w (deployedVsT w)
      (childBv (vsBoundAt Count.vsWordsOs vkBound) w) :=
  B1.Main.verifySubGoalsTB_of bytecode_length vsCompleteHyp_deployed hr hok

/-- **The aggregation guest is complete within the deployed budget**: for
every seed, statement and witness with `NodeRelation`, within the deployed limits, the caps
agreeing, no zero challenge where the guest divides, and the node's committed size at the budget
at most `2^30`, there is a valid execution of the guest on the statement's digest within the
verifier's size cap; each child's `verify_sub` charged `vsBoundAt Count.vsWordsOs vkBound` words
at its announced stack log and rate, and `vsCnt op` instructions of each opcode `op` there
(`vs_weight_le_deployed`). -/
theorem guest_complete :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  guest_complete_deployed (Pvs := deployedVsT)
    (fun _ _ _ hr _ hok => verifySubGoals_deployed hr hok)
    fun op _ _ hc _ _ _ _ hP hv hb => by
      obtain ⟨-, h20, h30, d, hd, hF⟩ := hP hc
      exact vs_weight_le_deployed op h20 h30 hd hF hv hb

end
end LeanVM.Guest.Budget
