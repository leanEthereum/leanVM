/-
  LeanVM.Guest.Budget.ClosedP

  `main` within the deployed budget with its tree's pops (`MainCompleteP`), every family's pops instantiated:
  each child's claim lists' digests popping their slots' pushes.
-/

module

public import LeanVM.Guest.Budget.DeployedBudget
public import LeanVM.Guest.Count.VsWordsOs
public import LeanVM.Guest.B1.Main.VerifySubGoals
public import LeanVM.Guest.B2C.RunsConsec
public import LeanVM.Guest.B1.Whir.CRecHos
public import LeanVM.Guest.B1.Place.ArmPops
public import LeanVM.Guest.B1.Place.OsFinal
public import LeanVM.Guest.B1.Main.L5RPops
public import LeanVM.Guest.B1.Main.MainPopsSR
public import LeanVM.Guest.B1.Main.MainGoalsClR
public import LeanVM.Guest.B1.Main.MainGoalsHClTBP

/-!
# `main` within the deployed budget, with its pops

* `deployedVsT`: child `c`'s `verify_sub` tree at the deployed instance, its stack log among `open_stacked`'s arms;
* `completeAtDTBR_lin_mono`: a callee's bounded completeness reading fewer words holds reading more;
* `pvH`: `verify_sub`'s honest entries for a child, its hints;
* `mainPopsD`: `main`'s callees' honest entries; `ChildListPopsHyp`, `childListPopsHyp`: each child's claim lists'
  digests popping their slots' pushes.
-/

namespace LeanVM.Guest.Budget

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Node
open LeanVM.Guest.End (bytecode)
open LeanVM.Guest.B1.VerifySub (vsTsAny vkBound)

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

end
end LeanVM.Guest.Budget

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest (DeployedLimits ChildrenOk)
open LeanVM.Guest.B1 (CompleteAtDTBR Returns RunsConsec)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vsTsAny vkBound vsExpLin vsArgs VsWordsOs VkCompleteAtBK)
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.Budget (deployedVsT)

@[expose] public section

/-- A callee's bounded completeness reading fewer words holds reading more. -/
theorem completeAtDTBR_lin_mono {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ} {f : String}
    {Lin Lin' : Layout} {args : List E} {Out : List E → Layout → Prop} {T : Reader → Tree → Prop} {B : ℕ}
    (hm : ∀ rd, MemL rd Lin' → MemL rd Lin) (hr : ∀ i, RegionL Lin i → RegionL Lin' i)
    (h : CompleteAtDTBR fs cert κ f Lin args Out T B) : CompleteAtDTBR fs cert κ f Lin' args Out T B := by
  intro fp
  obtain ⟨n, Lown, rets, Lout, hn, ho, hw, hd, hR⟩ := h fp
  refine ⟨n, Lown, rets, Lout, hn, ho, hw, hd, fun rd hl hM => ?_⟩
  obtain ⟨t, ⟨hn', hv, hb, hp, ht, hlo, hdd⟩, hT⟩ := hR rd hl (by
    rw [memL_append] at hM ⊢; exact ⟨hM.1, hm rd hM.2⟩)
  exact ⟨t, ⟨hn', hv, hb, hp, ht, loadsIn_mono t _ hr hlo, hdd⟩, hT⟩

/-- `verify_sub`'s honest entries for child `c`: its hints. -/
def pvH (bc : List K) (seed : Digest) (w : NodeWitness) (c : ℕ) : List Pop :=
  (w.children[c]?.map fun ch => Hints.childHints bc seed ch).getD []

end
end LeanVM.Guest.B1.Main

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Guest.End (bytecode bytecode_length)
open LeanVM.Guest.B1.Main (VerifySubGoalsTBR ChildListGoalsTBR hKid hMonoX hMonoS xPlan sPlan MainPops pvH)
open LeanVM.Guest.B1.VerifySub (vsBoundAt vkBound)

@[expose] public section

/-- **`main`'s callees' honest entries**: the claim lists', the duplicates', the raw signatures', the DA check's,
the children's (their claim lists' slots' pushes, `verify_sub`'s hints), the batching's. -/
noncomputable def mainPopsD (seed : Digest) (s : NodeStatement) (w : NodeWitness) : MainPops :=
  B1.Main.mainPopsH
    (fun _ => Hints.listPushes "claims" (s.claims.xmss.map fun c ↦ Hints.claimCells (xmssRoot c)
        (xmssParam c) c.2))
    (fun _ => Hints.listPushes "claims"
      (s.claims.sphincs.map fun c ↦ Hints.claimCells c.1.publicSeed c.1.root c.2))
    (fun _ => B1.Main.l5PopsH (fun c => Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun c => Hints.childSlotPushes ((sPlan s w).childSlots.getD c [])) (pvH bytecode seed w) s w) s w

/-- **Each child's claim lists' digests within `ccBM`, by trees of honest shape popping their slots' pushes**, at
the deployed frame sizes. -/
def ChildListPopsHyp : Prop :=
  ∀ seed s w, NodeRelation bytecode seed s w → GuestLimits s w →
    ChildListGoalsTBR B2C.fs B2C.cert 0 seed s w
      (fun rd c t => B1.Main.ccHonest (hKid s w c).ex (hMonoX s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((xPlan s w).childSlots.getD c []))
      (fun rd c t => B1.Main.ccHonest (hKid s w c).es (hMonoS s w c) t ∧
        t.pops coreProgram rd = Hints.childSlotPushes ((sPlan s w).childSlots.getD c []))
      (fun c => B1.Digest.ccBM B2C.fs Count.wSB (hMonoX s w c) (hKid s w c).ex)
      (fun c => B1.Digest.ccBM B2C.fs Count.wSB (hMonoS s w c) (hKid s w c).es)

/-- **`ChildListPopsHyp` holds** (`childListGoalsTBR_honest`). -/
theorem childListPopsHyp : ChildListPopsHyp := fun _ _ _ _ hl =>
  B1.Main.childListGoalsTBR_honest B2C.cert hl Count.mainStatics.ls

end
end LeanVM.Guest.Budget
