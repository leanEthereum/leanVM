/-
  LeanVM.Guest.Backend.Guest.Cpl.Budget

  The guest's completeness within the deployed budget at any instance of the honest memory whose
  cells place the frame runs, from `End.CompleteParts` at that instance: `Budget/Closed.lean`'s
  `guest_complete`, its proof generic in the cells.
-/

module

public import LeanVM.Guest.Budget.Final
public import LeanVM.Guest.Count.Instances
public import LeanVM.Guest.Budget.MvCount
public import LeanVM.Guest.Budget.L5Count
public import LeanVM.Guest.Count.VsWordsOs
public import LeanVM.Guest.B1.Main.VerifySubGoals
public import LeanVM.Guest.B1.VerifySub.CompleteHyp
public import LeanVM.Guest.B1.Sig.XmssSegComplete
public import LeanVM.Guest.B1.Sig.SphincsCompleteHolds
public import LeanVM.Guest.Deployed
public import LeanVM.Guest.AcceptableChild
public import LeanVM.Guest.EndComplete

/-!
# The deployed budget at any cells

`Budget/Closed.lean`'s `guest_complete` is stated at the certificates' cells only through its
proof: `MainComplete` (B1's, `Budget.mainComplete_budget`) is generic in the cells `cert`, given
that they fit the frame runs in their frames (`Lift.RunsFit`) at consecutive cells
(`B1.RunsConsec`), and `End.guest_complete_of_parts` is generic in the instance. So
`guest_complete_at`: at any instance `H C cert` whose `End.CompleteParts` follow from `MainComplete`
for every budget, and whose cells fit the runs, the guest is complete within
`deployedBudgetB (vsBoundAt Count.vsWordsOs vkBound)`, which is `Budget.deployedBudget`'s
definition (`Budget/DeployedBudget.lean`) written out, so that this module's import cone holds no
certificate check.
-/

namespace LeanVM.Guest.Backend.Cpl

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.Completeness LeanVM.Guest.Budget
open LeanVM.Node
open LeanVM.Guest.End (GuestCompleteWithin bytecode bytecode_length MainComplete)
open LeanVM.Guest.B1.Main (VerifySubGoalsTB childBv)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTsAny vkBound)

@[expose] public section

/-- **The deployed budget** (`Budget.deployedBudget`), `verify_sub`'s words `Bvf μ r` for a child
of announced stack log `μ` and rate `r`. -/
noncomputable def deployedBudgetB (Bvf : ℕ → ℕ → ℕ) : End.Budget :=
  mainBudget Deployed.fs Count.wSB Count.wSK Bvf (Deployed.ωArm Deployed.xmssArmC) Count.mainCounts l5C ccS vsCnt
    Deployed.jtSets

/-- **Child `c`'s `verify_sub` tree** (`Budget.deployedVsT`). -/
def deployedVsTB (w : NodeWitness) (c : ℕ) (t : Tree) : Prop :=
  ∀ hc : c < w.children.length,
    (childShape bytecode w.children[c]).1 - B1.Whir.minOpenLog < B1.Whir.openArms ∧
      (20 ≤ (childShape bytecode w.children[c]).1 ∧ (childShape bytecode w.children[c]).1 ≤ 30 ∧
        vsTsAny Deployed.fs Count.vsWordsOs vkBound (childShape bytecode w.children[c]).1
          (childShape bytecode w.children[c]).2 t)

variable {H : Inst → ℕ → E × E} {C : Inst → List (ℕ × E)} {cert : String → V → ℕ}

/-- **`verify_sub`'s completeness at the cells `cert`** (`Budget.vsCompleteHyp_deployed`). -/
theorem vsCompleteHyp_at (hrf : Lift.RunsFit Deployed.fs cert) (hcons : B1.RunsConsec cert) :
    B1.Main.VsCompleteHyp bytecode Deployed.fs cert 16
      (fun μ r t => 20 ≤ μ ∧ μ ≤ 30 ∧ vsTsAny Deployed.fs Count.vsWordsOs vkBound μ r t)
      (vsBoundAt Count.vsWordsOs vkBound) :=
  let h := B1.VerifySub.vsCompleteHyp_fs bytecode_length hrf hcons Count.vsWordsOs
  { complete := fun seed c sqE outE Lin hok hexp hout =>
      (h.complete seed c sqE outE Lin hok hexp hout).mono le_rfl
        fun _ ht => ⟨(h.shape seed c hok).1, (h.shape seed c hok).2.1, ht⟩
    shape := h.shape }

/-- **A child's `verify_sub` tree within `vsCnt`** at its announced stack log and rate
(`Budget.guest_complete`'s). -/
theorem vsWeightB : ∀ op (w : NodeWitness) c (hc : c < w.children.length) (rd : Reader) (t : Tree)
    (args rets : List E), deployedVsTB w c t → t.Valid coreProgram rd args rets → t.BufsOk coreProgram →
      t.weight (Deployed.ωArm Deployed.xmssArmC op) ≤
        vsCnt op (childShape bytecode w.children[c]).1 (childShape bytecode w.children[c]).2 :=
  fun op _ _ hc _ _ _ _ hP hv hb => by
    obtain ⟨-, h20, h30, d, hd, hF⟩ := hP hc
    exact vs_weight_le_deployed op h20 h30 hd hF hv hb

/-- **`MainComplete` at the cells `cert`** within the deployed budget (`Budget.guest_complete`'s
`MainComplete`). -/
theorem mainComplete_at (hrf : Lift.RunsFit Deployed.fs cert) (hcons : B1.RunsConsec cert) :
    MainComplete Deployed.fs cert Deployed.cnt (deployedBudgetB (vsBoundAt Count.vsWordsOs vkBound)) :=
  mainComplete_budget Deployed.fs cert Deployed.cnt (Deployed.ωArm Deployed.xmssArmC) Deployed.jtSets Count.mainCounts
    (Deployed.two_le_fs _) B1.Sig.verify_lean_xmss_complete_holds B1.Sig.sphincs_complete hrf
    Count.mainStatics
    (Pvs := deployedVsTB)
    (fun _ _ _ hr _ hok => B1.Main.verifySubGoalsTB_of bytecode_length (vsCompleteHyp_at hrf hcons) hr hok)
    (Deployed.cnt_le_weight_arm Deployed.xmssArmC Deployed.xmssArmC_spec) l5C ccS vsCnt
    fun _ _ _ _ hl op _ _ _ _ _ hv hb hT => l5_honest_weight_le op hl (vsWeightB op _) hv hb hT

/-- **The guest is complete within the deployed budget** at any instance `H C cert` whose pieces of
completeness follow from `main`'s and whose cells fit the frame runs: `Budget.guest_complete`'s
statement (`deployedBudgetB` is `Budget.deployedBudget`). -/
theorem guest_complete_at
    (hparts : ∀ b, MainComplete Deployed.fs cert Deployed.cnt b → End.CompleteParts Deployed.fs H C cert Deployed.cnt b)
    (hrf : Lift.RunsFit Deployed.fs cert) (hcons : B1.RunsConsec cert) :
    GuestCompleteWithin (deployedBudgetB (vsBoundAt Count.vsWordsOs vkBound)) :=
  End.guest_complete_of_parts (hparts _ (mainComplete_at hrf hcons))

end
end LeanVM.Guest.Backend.Cpl
