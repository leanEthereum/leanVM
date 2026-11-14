/-
  LeanVM.Guest.Budget.MainExact

  `MainExactHyp`, proved: `main`'s families complete by trees exact at every node, with no hypothesis left.
-/

module

public import LeanVM.Guest.Budget.ClosedPE
public import LeanVM.Guest.B1.KeccakGkr.VkCWE

/-!
# `main` exact

`mainExactHyp`: `MainExactHyp` from `verify_keccak`'s exact form (`verify_keccak_completeAtBE_fs`) through
`mainExactHypL5_of_vk` and `mainExactHyp_of_l5`. `mainCompletePE_deployed_proved`: `main` complete within the deployed
budget with its pops, every node exact.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The children's loop, every node exact.** -/
theorem mainExactHypL5 : MainExactHypL5 :=
  mainExactHypL5_of_vk (B1.VerifySub.verify_keccak_completeAtBE_fs (by norm_num))

/-- **`main`'s families still open, every node exact**: `MainExactHyp`, with no hypothesis. -/
theorem mainExactHyp : MainExactHyp := mainExactHyp_of_l5 mainExactHypL5

/-- **`main` is complete within the deployed budget with its pops, every node exact.** -/
theorem mainCompletePE_deployed_proved :
    MainCompletePE B2C.fs B2C.cert B2C.cnt (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  mainCompletePE_deployed mainExactHyp

end
end LeanVM.Guest.Budget
