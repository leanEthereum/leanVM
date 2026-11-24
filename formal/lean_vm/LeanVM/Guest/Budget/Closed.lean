/-
  LeanVM.Guest.Budget.Closed

  **The guest is complete within the deployed budget**, from `main`'s completeness with every node exact
  (`mainCompletePE_deployed`, `mainExactHyp`), its pops and exactness forgotten.
-/

module

public import LeanVM.Guest.Budget.MainExact
public import LeanVM.Guest.Budget.Fits

namespace LeanVM.Guest.Budget

open LeanVM.Guest.Completeness
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The aggregation guest is complete within the deployed budget**: for
every seed, statement and witness with `NodeRelation`, within the deployed limits, the caps
agreeing, and the node's committed size at the budget
at most `2^30`, there is a valid execution of the guest on the statement's digest within the
verifier's size cap; each child's `verify_sub` charged `vsBoundAt Count.vsWordsOs vkBound` words
at its announced stack log and rate, and `vsCnt op` instructions of each opcode `op` there
(`vs_weight_le_deployed`). -/
theorem guest_complete :
    GuestCompleteWithin (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  B2C.guest_complete_b2c (mainCompletePE_deployed mainExactHyp).toP.toMain

/-- **The aggregation guest is complete within the deployed budget**, `verify_sub`'s words for a
child of announced stack log `μ` and rate `r` `deployedBvAt μ r`: the budget's words
`Count.deployedWords deployedBvAt`, its instructions `Count.deployedInstrs op`. -/
theorem guest_complete_numeric : GuestCompleteWithin (deployedBudget deployedBvAt) :=
  guestComplete_mono guest_complete fun _ _ w _ _ hok => deployedBudget_size_mono _
    fun p hp => by
      obtain ⟨ch, hch, rfl⟩ :=
        List.mem_map.mp (show p ∈ w.children.map (childShape bytecode) from hp)
      obtain ⟨h1, h2, h3, h4⟩ := B1.Main.childShape_bounds End.bytecode_length hok hch
      exact (vsBoundAt_eq_deployedBvAt h1 h2 h3 h4).le

/-- **Every node within the deployed limits has a valid execution of the guest**
(`GuestCompleteOnAcceptableChildren`). -/
theorem guest_complete_on_acceptable_children : GuestCompleteOnAcceptableChildren :=
  fun seed s w hrel hlim hok ↦
    guest_complete_numeric seed s w hrel (GuestLimits.of_limits hlim hrel.1) hok (size_le hlim hrel.1)

end
end LeanVM.Guest.Budget
