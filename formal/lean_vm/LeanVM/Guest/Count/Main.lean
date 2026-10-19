/-
  LeanVM.Guest.Count.Main

  The weights of `main`'s callees at each opcode's instructions: `MainWeightHyps` at
  `B2C.ωArm B1.Sig.xmssArmC op` (`verify_lean_xmss`'s arms counted separately).
-/

module

public import LeanVM.Guest.Count.Static
public import LeanVM.Guest.Count.OsStatic
public import LeanVM.Guest.Count.Ratio
public import LeanVM.Guest.B1.Main.WeightLoop
public import LeanVM.Guest.B1.Sig.ArmCostB2C
public import LeanVM.Guest.B2C.CntWeight

/-!
# `main`'s callees' counts

`kcWt op : MainWeightHyps B2C.fs (B2C.ωArm B1.Sig.xmssArmC op)`: the statically bounded callees by
their certificates at `kcOm op` (`Count/Static`), `claim_list_digest` and `child_claim_list_digest` within their
ratios of their words (`Count/Ratio`), `verify_sub`'s statically bounded callees by theirs
(`Count/OsStatic`); `da_verify`'s and `verify_sub`'s weights ride their completeness.
-/

namespace LeanVM.Guest.Count

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest
open LeanVM.Guest.B1.Main (MainWeightHyps)

@[expose] public section

/-- The frame weights `kcOm` are `ωArm` at `verify_lean_xmss`'s arms. -/
theorem ωArm_xmssArmC (op : Opcode) : B2C.ωArm B1.Sig.xmssArmC op = kcOm op := by
  funext f
  unfold B2C.ωArm kcOm
  rw [B1.Sig.xmssArmC_val]
  cases op <;> rfl

/-- **The weights of `main`'s callees** at `op`'s instructions, `verify_lean_xmss`'s arms counted
separately (`B2C.ωArm B1.Sig.xmssArmC`). -/
noncomputable def kcWt (op : Opcode) : MainWeightHyps B2C.fs (B2C.ωArm B1.Sig.xmssArmC op) where
  Bexp := kcExp op
  exp := by rw [ωArm_xmssArmC]; exact kcExp_weightLe op
  Kl0 := kcL0 op
  l0 := by rw [ωArm_xmssArmC]; exact kcL0_loop op
  Kl1 := kcL1 op
  l1 := by rw [ωArm_xmssArmC]; exact kcL1_loop op
  Kl2 := kcL2 op
  l2 := by rw [ωArm_xmssArmC]; exact kcL2_loop op
  Kl3 := kcL3 op
  l3 := by rw [ωArm_xmssArmC]; exact kcL3_loop op
  Kl4 := kcL4 op
  l4 := by rw [ωArm_xmssArmC]; exact kcL4_loop op
  Kl100 := kcL100 op
  l100 := by rw [ωArm_xmssArmC]; exact kcL100_loop op
  Bdl := kcDl op
  dl := by rw [ωArm_xmssArmC]; exact kcDl_weightLe op
  Bcov := kcCov op
  cov := by rw [ωArm_xmssArmC]; exact kcCov_weightLe op
  cAgg := kcAggC op
  dAgg := kcAggD op
  agg := by rw [ωArm_xmssArmC]; exact kcAgg_le op
  Bsd := kcSd op
  sd := by rw [ωArm_xmssArmC]; exact kcSd_weightLe op
  αcl := krClA op
  cl := by rw [ωArm_xmssArmC]; exact krCl_weight op
  αccl := krCclA op
  ccl := by rw [ωArm_xmssArmC]; exact krCcl_weight op
  vsc := ⟨kcoGpw op, kcoL2a op, kcoL2b op, kcoAc op, kcoPl op, kcoOs op⟩
  vsOk := by
    rw [ωArm_xmssArmC]
    exact ⟨kcoGpw_weightLe op, kcoL2a_weightLe op, kcoL2b_weightLe op, kcoAc_weightLe op, kcoPl_weightLe op,
      fun μ r _ _ _ _ => kcoOs_weightLe op (μ - 22 + 7 * (r - 1)) (by omega)⟩

end
end LeanVM.Guest.Count
