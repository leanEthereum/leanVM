/-
  LeanVM.Guest.Budget.ClosedPE

  `main` within the deployed budget with its tree's pops and every node exact (`MainCompletePE`), given the E forms
  of the families still open.
-/

module

public import LeanVM.Guest.Budget.ClosedP
public import LeanVM.Guest.Budget.FinalPE
public import LeanVM.Guest.B1.Main.MainLoop3E
public import LeanVM.Guest.Exact.MainLoop2
public import LeanVM.Guest.B1.Main.L5E
public import LeanVM.Guest.B1.Main.VsDeployedE

/-!
# `main` within the deployed budget, every node exact

`MainExactHyp`: at the deployed instance, `main_loop2`, `main_loop3` and the children's loop complete by trees of their predicates
whose every node is exact (`MainGoalsRE`). `mainCompletePE_deployed`: `mainCompleteP_deployed` with every node of
`main`'s tree exact, from it; `aggregate_claims` by `mainGoalsRR_agE`, the other callees exact for free.

`MainExactHypL5`: `MainExactHyp`'s children's loop alone. `mainExactHyp_of_l5`: `main_loop2` is exact for free
(`main_loop2_exactFree`, checked by chunks) and `main_loop3` by `mainGoalsRE_l4`, so `MainExactHyp` follows;
`mainCompletePE_deployedL5`: `mainCompletePE_deployed` from it.

`VsExactHyp`: each child's `verify_sub` call at the deployed instance by a tree also exact; `mainExactHypL5_of_vs`:
`MainExactHypL5` from it (`mainGoalsRR_l5E`); `vsExactHyp_of`: `VsExactHyp` from `verify_sub`'s callees with computed
hints exact (`VsKidsExact`, `verifySubGoalsTBR_deployedE`).
-/

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.B1.Main (VerifySubGoalsTBR ChildListGoalsTBR hKid hMonoX hMonoS xPlan sPlan MainPops pvH
  verifySubGoalsTBR_deployed)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **The families still open, every node exact**: at the deployed instance, `main_loop2`, `main_loop3` and the children's loop
complete by trees of their predicates whose every node is exact on the memory. -/
def MainExactHyp : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
    B1.Main.MainGoalsRE B2C.fs B2C.cert 0 seed s w Count.wSK
      (B1.Main.mainPredsHP B2C.fs Count.wSB Count.wSK (B1.Main.childBv (vsBoundAt Count.vsWordsOs vkBound) w)
        (deployedVsT w) s w (mainPopsD seed s w))
      (B1.Main.mainBsH B2C.fs Count.wSB Count.wSK (B1.Main.childBv (vsBoundAt Count.vsWordsOs vkBound) w) s w)

/-- **`main` is complete within the deployed budget with its pops, every node exact**, given the E forms of
`main_loop2`, `main_loop3` and the children's loop (`MainExactHyp`). -/
theorem mainCompletePE_deployed (hE : MainExactHyp) :
    MainCompletePE B2C.fs B2C.cert B2C.cnt (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  mainComplete_budgetPE B2C.fs B2C.cert B2C.cnt (Pvs := deployedVsT) (Q := mainPopsD)
    (B2C.ωArm B2C.xmssArmC) B2C.jtSets Count.mainCounts (B2C.two_le_fs _)
    B1.Sig.verify_lean_xmss_complete_holds B1.Sig.sphincs_complete Count.mainStatics
    (fun _ _ _ _ hl _ => ⟨B1.Main.mainPopsS_l1 hl fun _ => rfl, B1.Main.mainPopsS_l2 hl fun _ => rfl⟩)
    (fun _ _ _ hr hl hok =>
      { clx := B1.Main.mainGoalClXR hl Count.mainStatics fun _ => rfl
        cls := B1.Main.mainGoalClSR hl Count.mainStatics fun _ => rfl
        l3 := B1.Main.mainGoalsRR_l3 hr hl Count.mainStatics.main fun _ => rfl
        l4 := B1.Main.mainGoalsRR_l4 hr hl Count.mainStatics.main fun _ => rfl
        dv := B1.Main.mainGoalsRR_dv B2C.fs B2C.cert 0 hr B2C.runsFit Count.mainStatics fun _ => rfl
        l5 := B1.Main.mainGoalsRR_l5 bytecode_length hr hl Count.mainStatics
          (verifySubGoalsTBR_deployed hr hok) (childListPopsHyp _ _ _ hr hl) fun _ => rfl
        ag := B1.Main.mainGoalsRR_ag B2C.fs B2C.cert 0 bytecode_length hr hl Count.mainStatics fun _ => rfl })
    hE (fun _ _ _ hr hl => B1.Main.mainGoalsRR_agE B2C.fs B2C.cert 0 bytecode_length hr hl Count.mainStatics fun _ => rfl)
    (fun _ _ _ hr hl rd =>
      ⟨B1.Main.mainSegs_cx (fun _ => rfl) rd, B1.Main.mainSegs_cs (fun _ => rfl) rd,
        B1.Main.mainSegs_d0 (fun _ => rfl) rd, B1.Main.mainSegs_d1 (fun _ => rfl) rd,
        B1.Main.mainSegs_r2 hr hl (fun _ => rfl) rd, B1.Main.mainSegs_r3 hr hl (fun _ => rfl) rd,
        B1.Main.mainSegs_da hr (fun _ => rfl) rd, B1.Main.mainSegs_kids hl (fun _ => rfl) rd,
        B1.Main.mainSegs_agg (fun _ => rfl) rd⟩)
    (B2C.cnt_le_weight_arm B2C.xmssArmC B2C.xmssArmC_spec) l5C ccS vsCnt
    fun _ _ _ _ hl op _ _ _ _ _ hv hb hT =>
      l5_honest_weight_le op hl (fun _ hc _ _ _ _ hP hv hb => by
        obtain ⟨-, h20, h30, d, hd, hF⟩ := hP hc
        exact vs_weight_le_deployed op h20 h30 hd hF hv hb) hv hb hT

/-- **The children's loop, every node exact**: `MainExactHyp`'s field still open, at the deployed instance. -/
def MainExactHypL5 : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w → ChildrenOk bytecode seed w →
    (B1.Main.hm B2C.fs 0 seed s w).nc ≠ 0 →
    B1.CompleteAtDTBR B2C.fs B2C.cert 23 name% «main_loop4» (B1.Main.hLmain B2C.fs 0 seed s w)
      [1, gen ^ (B1.Main.hm B2C.fs 0 seed s w).nc, (B1.Main.hm B2C.fs 0 seed s w).a409,
        (B1.Main.hm B2C.fs 0 seed s w).a77, (B1.Main.hm B2C.fs 0 seed s w).a117,
        gen ^ ((B1.Main.hm B2C.fs 0 seed s w).nlx + (B1.Main.hm B2C.fs 0 seed s w).nxd),
        (B1.Main.hm B2C.fs 0 seed s w).a80,
        (B1.Main.hm B2C.fs 0 seed s w).a117 *
          gen ^ ((B1.Main.hm B2C.fs 0 seed s w).nlx + (B1.Main.hm B2C.fs 0 seed s w).nxd),
        gen ^ ((B1.Main.hm B2C.fs 0 seed s w).nls + (B1.Main.hm B2C.fs 0 seed s w).nsd),
        (B1.Main.hm B2C.fs 0 seed s w).a406, (B1.Main.hm B2C.fs 0 seed s w).aDa,
        (digestHalves (B1.Main.hm B2C.fs 0 seed s w).seed).1, (digestHalves (B1.Main.hm B2C.fs 0 seed s w).seed).2,
        (B1.Main.hm B2C.fs 0 seed s w).a394, (B1.Main.hm B2C.fs 0 seed s w).et,
        (B1.Main.hm B2C.fs 0 seed s w).a400] (B1.Returns [])
      (B1.Main.mainPredsHP B2C.fs Count.wSB Count.wSK (B1.Main.childBv (vsBoundAt Count.vsWordsOs vkBound) w)
        (deployedVsT w) s w (mainPopsD seed s w)).withExact.P5
      (B1.Main.mainBsH B2C.fs Count.wSB Count.wSK (B1.Main.childBv (vsBoundAt Count.vsWordsOs vkBound) w) s w).B5

/-- **`MainExactHyp` from the children's loop alone**: `main_loop2` exact for free, `main_loop3` by
`mainGoalsRE_l4`. -/
theorem mainExactHyp_of_l5 (h : MainExactHypL5) : MainExactHyp := fun seed s w hr hl hok =>
  { l3 := fun h0 => (B1.Main.mainGoalsRR_l3 hr hl Count.mainStatics.main (fun _ => rfl) h0).andEvery
      (B1.everyOn_exact main_loop2_exactFree)
    l4 := B1.Main.mainGoalsRE_l4 hr hl Count.mainStatics.main fun _ => rfl
    l5 := h seed s w hr hl hok }

/-- **`main` is complete within the deployed budget with its pops, every node exact**, given the children's loop
(`MainExactHypL5`). -/
theorem mainCompletePE_deployedL5 (h : MainExactHypL5) :
    MainCompletePE B2C.fs B2C.cert B2C.cnt (deployedBudget (vsBoundAt Count.vsWordsOs vkBound)) :=
  mainCompletePE_deployed (mainExactHyp_of_l5 h)

/-- **Each child's `verify_sub` call at the deployed instance, every node exact**: `verifySubGoalsTBR_deployed`'s trees
also exact on the memory. -/
def VsExactHyp : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → ChildrenOk bytecode seed w →
    VerifySubGoalsTBR B2C.fs B2C.cert 0 seed s w
      (fun rd c t ↦ (deployedVsT w c t ∧ SameStreams (t.pops coreProgram rd) (pvH bytecode seed w c)) ∧
        t.Every (ExactAt coreProgram rd))
      (B1.Main.childBv (vsBoundAt Count.vsWordsOs vkBound) w)

/-- **The children's loop, every node exact**, given each child's `verify_sub` call's trees exact. -/
theorem mainExactHypL5_of_vs (h : VsExactHyp) : MainExactHypL5 := fun seed s w hr hl hok =>
  B1.Main.mainGoalsRR_l5E bytecode_length hr hl Count.mainStatics (h seed s w hr hok)
    (childListPopsHyp _ _ _ hr hl) fun _ => rfl

/-- **`VsExactHyp` from `verify_sub`'s callees with computed hints exact** at `B2C.fs`. -/
theorem vsExactHyp_of
    (hK : B1.VerifySub.VsKidsExact B2C.fs B2C.cert 16 Count.vsWordsOs vkBound) : VsExactHyp :=
  fun _ _ _ hr hok => B1.Main.verifySubGoalsTBR_deployedE hK hr hok

/-- **The children's loop, every node exact**, given `verify_sub`'s callees with computed hints exact. -/
theorem mainExactHypL5_of_kids
    (hK : B1.VerifySub.VsKidsExact B2C.fs B2C.cert 16 Count.vsWordsOs vkBound) : MainExactHypL5 :=
  mainExactHypL5_of_vs (vsExactHyp_of hK)

end
end LeanVM.Guest.Budget
