/-
  LeanVM.Guest.Count.Main

  The weights of `main`'s callees at each opcode's instructions: `MainWeightHyps` at
  `B2C.pathMax · op`.
-/

module

public import LeanVM.Guest.Count.Static
public import LeanVM.Guest.Count.Ratio
public import LeanVM.Guest.B1.Main.WeightLoop

/-!
# `main`'s callees' counts

`kcWt op : MainWeightHyps B2C.fs (B2C.pathMax · op)`: the statically bounded callees by their
certificates (`Count/Static`), `claim_list_digest`, `child_claim_list_digest`, `da_verify` and
`verify_sub` within their ratios of their words (`Count/Ratio`).
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1.Main (MainWeightHyps)

@[expose] public section

/-- **The weights of `main`'s callees** at `op`'s instructions. -/
def kcWt (op : Opcode) : MainWeightHyps B2C.fs (B2C.pathMax · op) where
  Bexp := kcExp op
  exp := kcExp_weightLe op
  Kl0 := kcL0 op
  l0 := kcL0_loop op
  Kl1 := kcL1 op
  l1 := kcL1_loop op
  Kl2 := kcL2 op
  l2 := kcL2_loop op
  Kl3 := kcL3 op
  l3 := kcL3_loop op
  Kl4 := kcL4 op
  l4 := kcL4_loop op
  Kl100 := kcL100 op
  l100 := kcL100_loop op
  Bdl := kcDl op
  dl := kcDl_weightLe op
  Bcov := kcCov op
  cov := kcCov_weightLe op
  cAgg := kcAggC op
  dAgg := kcAggD op
  agg := kcAgg_le op
  Bsd := kcSd op
  sd := kcSd_weightLe op
  αcl := krClA op
  cl := krCl_weight op
  αccl := krCclA op
  ccl := krCcl_weight op
  αvs := krVsA op
  vs := krVs_weight op

end
end LeanVM.Guest.Count
