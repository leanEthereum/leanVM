/-
  LeanVM.Guest.B2C.DeployedEq

  The certificates' frame sizes and counts are the back end's: `B2C.fs`, `B2C.cnt`, `B2C.ωArm`,
  `B2C.xmssArmC`, `B2C.jtSets` and what they are made of equal their `Deployed` forms.
-/

module

public import LeanVM.Guest.B2C.ArmBound
public import LeanVM.Guest.Deployed

/-!
# The certificates' tables are the back end's

While the back end reproduces the Rust compiler, the tables `guest-cert` writes from the
certificates (`Data.frameSizes`, `Data.mainCells`, `Data.jtSlots`, the plumbs' `pmax`,
`Data.cplArms`, `Data.armFn`, `Data.armMax`) are the ones `guest-tables` writes from the back end's
placement (`Deployed.Data`), value for value (the kernel compares them). So every definition of
the completeness budget over the certificates equals its `Deployed` form: `fs_deployed`,
`cnt_deployed`, `ωArm_deployed`, `xmssArmC_deployed`, `jtSets_deployed`, and the pieces between.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-! ## The tables -/

set_option maxRecDepth 100000 in
theorem frameSizes_deployed : Data.frameSizes = Deployed.Data.frameSizes := by decide +kernel

theorem mainCells_deployed : Data.mainCells = Deployed.Data.mainCells := rfl

theorem jtSlots_deployed : Data.jtSlots = Deployed.Data.jtSlots := rfl

theorem armFn_deployed : Data.armFn = Deployed.Data.armFn := rfl

theorem armMax_deployed : Data.armMax = Deployed.Data.armMax := by decide +kernel

set_option maxRecDepth 100000 in
theorem cplArms_deployed : Data.cplArms = Deployed.Data.arms := by decide +kernel

set_option maxRecDepth 100000 in
theorem plumbs_pmax_deployed : Data.plumbs.map Plumb.pmax = Deployed.Data.pmax := by decide +kernel

/-! ## The definitions -/

private theorem map_listElementOrDefault {α β : Type} (f : α → β) :
    ∀ (l : List α) (j : ℕ) (d : α), f (listElementOrDefault l j d) = (l.map f).getD j (f d)
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: l, j + 1, d => map_listElementOrDefault f l j d

theorem idxOf_deployed : idxOf = Deployed.idxOf := rfl

theorem entryOf_deployed : entryOf = Deployed.entryOf := rfl

theorem mainFrame_deployed : mainFrame = Deployed.mainFrame := rfl

theorem fsAt_deployed : fsAt = Deployed.fsAt := by
  funext j
  unfold fsAt Deployed.fsAt
  rw [frameSizes_deployed]

theorem fs_deployed : fs = Deployed.fs := by
  funext f
  unfold fs Deployed.fs
  rw [fsAt_deployed, mainFrame_deployed]
  rfl

theorem fsN_deployed : fsN = Deployed.fsN := by
  funext j
  unfold fsN Deployed.fsN
  rw [fsAt_deployed, mainFrame_deployed]

theorem jtSets_deployed : jtSets = Deployed.jtSets := rfl

theorem opIdx_deployed : opIdx = Deployed.opIdx := by
  funext op
  cases op <;> rfl

/-- The certificates' path maxima are the back end's. -/
theorem pmax_deployed (j : ℕ) : (plumbOf j).pmax = Deployed.pmaxOf j := by
  unfold plumbOf Deployed.pmaxOf
  rw [map_listElementOrDefault Plumb.pmax, plumbs_pmax_deployed]

theorem pathMax_deployed : pathMax = Deployed.pathMax := by
  funext f op
  unfold pathMax Deployed.pathMax
  rw [idxOf_deployed]
  cases Deployed.idxOf f with
  | none => rfl
  | some j => show (plumbOf j).pmax.getD (opIdx op) 0 = _; rw [pmax_deployed, opIdx_deployed]

theorem dedupC_deployed : ∀ L : List (ℕ × E), dedupC L = Deployed.dedupC L
  | [] => rfl
  | q :: qs => by rw [dedupC, Deployed.dedupC, dedupC_deployed qs]

theorem frameE_deployed : frameE = Deployed.frameE := by
  funext n L
  unfold frameE Deployed.frameE
  rw [dedupC_deployed]

mutual
theorem cost1_deployed (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ s : Stmt, cost1 acs σ s = Deployed.cost1 acs σ s
  | .atom _ => rfl
  | .ite _ z n => by rw [cost1, Deployed.cost1, costW_deployed acs σ z, costW_deployed acs σ n]
  | .match_ x arms => by rw [cost1, Deployed.cost1, costArms_deployed acs σ x _ 0 arms]
  | .call .. => rfl
  | .callIf .. => rfl
  | .dispatch .. => rfl
  | .ret _ => rfl

theorem costW_deployed (acs : List (ℕ × List (List ℕ))) (σ : Val) :
    ∀ ss : List Stmt, costW acs σ ss = Deployed.costW acs σ ss
  | [] => rfl
  | s :: ss => by rw [costW, Deployed.costW, cost1_deployed acs σ s, costW_deployed acs σ ss]

theorem costArms_deployed (acs : List (ℕ × List (List ℕ))) (σ : Val) (x : V)
    (key : Option (List (List ℕ))) : ∀ (k : ℕ) (arms : List (List Stmt)),
      costArms acs σ x key k arms = Deployed.costArms acs σ x key k arms
  | _, [] => rfl
  | k, a :: as => by
    rw [costArms, Deployed.costArms, costW_deployed acs σ a, costArms_deployed acs σ x key (k + 1) as,
      opIdx_deployed]
    rfl
end

theorem pathCount_deployed : pathCount = Deployed.pathCount := by
  funext j σ op
  unfold pathCount Deployed.pathCount
  rw [pmax_deployed, opIdx_deployed, cplArms_deployed, costW_deployed]

theorem pathCountN_deployed : pathCountN = Deployed.pathCountN := by
  funext f σ op
  unfold pathCountN Deployed.pathCountN
  rw [idxOf_deployed, pathCount_deployed]
  rfl

mutual
theorem weightV_deployed (ω : String → Val → ℕ) : ∀ t : Tree, weightV ω t = Deployed.weightV ω t
  | .node f σ _ kids => by rw [weightV, Deployed.weightV, weightVKids_deployed ω kids]
  | .phantom .. => by rw [weightV, Deployed.weightV]

theorem weightVKids_deployed (ω : String → Val → ℕ) :
    ∀ ks : List Tree, weightVKids ω ks = Deployed.weightVKids ω ks
  | [] => by rw [weightVKids, Deployed.weightVKids]
  | k :: ks => by
    rw [weightVKids, Deployed.weightVKids, weightV_deployed ω k, weightVKids_deployed ω ks]
end

/-- **The certificates' instruction counts are the back end's.** -/
theorem cnt_deployed : cnt = Deployed.cnt := by
  funext T op
  unfold cnt Deployed.cnt
  rw [weightV_deployed, pathCountN_deployed, jtSets_deployed]

theorem ωArm_deployed : ωArm = Deployed.ωArm := by
  funext C op f
  unfold ωArm Deployed.ωArm
  rw [pathMax_deployed]

theorem xmssArmC_deployed : xmssArmC = Deployed.xmssArmC := by
  funext op
  unfold xmssArmC Deployed.xmssArmC
  rw [armMax_deployed, opIdx_deployed]

end
end LeanVM.Guest.B2C
