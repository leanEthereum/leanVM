module

public import LeanVM.Guest.Limits

/-!
# The guest's limits from the deployed ones

`GuestLimits` (what the guest's completeness proofs take) from `NodeRelation` and Hotwire's
`DeployedLimits`: the signature claims held are `NodeRelation`'s, and the memory budget at most
`2^24` words bounds the coverage table, `46` words a child's claim and at least `1400` a raw
signature, below `2^19` slots (`GuestLimits.of_deployed`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Parameters LeanVM.Node LeanVM.Protocol

@[expose] public section

/-- **The coverage table is below `2^19` slots** within the memory budget. -/
theorem coverageSlots_lt_of_budget {w : NodeWitness} (h : w.memoryBudget ≤ 2 ^ 24) :
    coverageSlots w < 2 ^ 19 := by
  unfold NodeWitness.memoryBudget NodeWitness.childClaimCount at h
  unfold coverageSlots
  omega

/-- **`GuestLimits` from `NodeRelation` and the deployed limits.** -/
theorem GuestLimits.of_deployed {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (hrel : NodeRelation bytecode seed s w) (hlim : DeployedLimits s w) :
    GuestLimits s w :=
  { hlim with
    signatureClaimsHeld := hrel.1
    coverageSlotsBelow2Pow23 :=
      lt_of_lt_of_le (coverageSlots_lt_of_budget hlim.withinMemoryBudget) (by norm_num) }

end
end LeanVM.Guest.Complete
