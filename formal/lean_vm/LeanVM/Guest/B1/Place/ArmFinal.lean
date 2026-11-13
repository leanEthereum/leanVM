/-
  LeanVM.Guest.B1.Place.ArmFinal

  `open_stacked` complete placed at every stack log and rate, from the body's honest data and the
  helpers' placed statements.
-/

module

public import LeanVM.Guest.B1.Place.ArmLift
public import LeanVM.Guest.B1.Place.LpProof
public import LeanVM.Guest.B1.Place.LqProof
public import LeanVM.Guest.B1.Place.LqBoundP
public import LeanVM.Guest.B1.Place.OsMeanB
public import LeanVM.Guest.B1.Whir.Sound

/-!
# `open_stacked`, placed, every arm

`HelperBounds`: each helper of the tables is complete placed within any bound of its valid trees
(`TotalLe`). `open_stacked_completeAtOT_of`: the arm of `μ`, called on the rate's selector, is
complete placed at an optional words bound (`osBosAt`) by its node, from `arm_completeAtO`, the
body's honest data `H`, the named callees (`kindD_holds`, or `kindDB` within `OsLeafBounds`), and
the helpers (`level_positions_completeAt`, `level_queries_completeAtOP`, `level_residual`'s
statement, or `HelperBounds`); `open_stacked_completeAtO_of` with `H` from `os_honest_Spec`. `open_stacked_completeAtD_of`, `open_stacked_completeAtB_of`: the two
statements of `Place/OsSpec`.
-/

namespace LeanVM.Guest.B1.Arm

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 LeanVM.Guest.B1.Whir
open LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- **The helpers within the bounds of their trees**: each entry of `lpTable`, `lqTable` and
`lrTable` is complete placed within any `B` bounding its valid trees. -/
def HelperBounds (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) : Prop :=
  (∀ e ∈ lpTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
    LpAtO fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (some B)) ∧
  (∀ e ∈ lqTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
    LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 (some B)) ∧
  (∀ e ∈ lrTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
    LrAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (some B))

theorem osCalleeNames_rate {m ri : ℕ} :
    osCalleeNames (osCfgR m ri) = osCalleeNames (osCfg m) := by
  unfold osCalleeNames osCallees; rw [← osBody_rate m ri]

theorem osSizesL_rate (m ri : ℕ) : osSizesL (osCfgR m ri) = osSizesL (osCfg m) := by
  have hmap : (osCfgR m ri).levels.map OsLv.folds = (osCfg m).levels.map OsLv.folds := by
    simp only [osCfgR, osCfg, OsCfg.withLevels, osLevelsR, List.map_map]
    rfl
  have hlen : (osCfgR m ri).levels.length = (osCfg m).levels.length := by
    simpa using congrArg List.length hmap
  have hg : ∀ c : OsCfg, (c.levels.getD c.yrLevel default).folds =
      (c.levels.map OsLv.folds).getD c.yrLevel (default : OsLv).folds := fun c ↦ by
    rw [List.getD_map]
  have ht : ∀ c : OsCfg, (c.levels.take c.yrLevel).map (fun lv ↦ 2 + lv.folds) =
      ((c.levels.map OsLv.folds).take c.yrLevel).map (fun x ↦ 2 + x) := fun c ↦ by
    simp [List.map_take, List.map_map, Function.comp_def]
  unfold osSizesL
  dsimp only
  rw [hg (osCfgR m ri), hg (osCfg m), ht (osCfgR m ri), ht (osCfg m), hmap, hlen]
  rfl

theorem osBos_rate {m ri : ℕ} (fs' Bk : String → ℕ)
    (name : String) : osBos fs' Bk name (osCfgR m ri) = osBos fs' Bk name (osCfg m) := by
  unfold osBos osKidsB osCallees; rw [osSizesL_rate, ← osBody_rate m ri]

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **`open_stacked` is complete placed at an optional words bound by its node**, from the body's honest data `H`,
within each bound its levels' `level_queries` popping their honest entries. -/
theorem open_stacked_completeAtOT_of (hLR : level_residual_completeAt_Spec)
    {μ r : ℕ} (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {Bd : Option (String → ℕ)} (hleaf : ∀ Bk ∈ Bd, OsLeafBounds fs Bk)
    (hHB : ∀ Bk ∈ Bd, HelperBounds fs cert κ)
    {S : KeccakState} {root : Digest} {target cur tabs : E} {xs : List E} {w : WhirEnd}
    (H : OsHonestA (osCfgR (μ - minOpenLog) (r - 1))
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
      cur tabs xs w.target w.inner w.residual (w.point ++ List.replicate (pointCap - μ) 0)
      (w.point.map (1 + ·) ++ List.replicate (pointCap - μ) 1))
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    ∃ fn : Fn, coreProgram.find? (openName μ) = some fn ∧ fn.body = osBody (osCfgR (μ - minOpenLog) (r - 1)) ∧
      CompleteAtOT fs cert κ (openName μ) Lin
        (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
        (OsOut μ w) (Bd.map fun Bk ↦ osBosAt fs Bk μ)
        (FlatNodeT (openName μ) fn (osBodyA (osCfgR (μ - minOpenLog) (r - 1)))
          (fun σ ↦ σ (.n osRate) = ofK (addressOfIndex (r - 1))) (armTs (Bd := Bd) H)) := by
  revert H
  set m := μ - minOpenLog with hmd
  set ri := r - 1 with hrid
  intro H
  have hm : m < 11 := by simp only [hmd, minOpenLog]; omega
  have hri : ri < 4 := by omega
  have hd : FnIs ("open_stacked__L" ++ natStr m) (osParams 11) (osBody (osCfgR m ri)) := by
    have := osData_all m hm
    unfold OsData at this
    rwa [osBody_rate m ri] at this
  obtain ⟨fn, hf, hps, hbody⟩ := hd
  have hf' : coreProgram.find? (openName μ) = some fn := by rw [openName_eq hm]; exact hf
  have hTot : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri), TotalLe coreProgram fs f (fun _ ↦ Bk f) :=
    fun Bk hBk f hf ↦ hleaf Bk hBk m hm f (by rwa [osCalleeNames_rate] at hf)
  have hnamed : ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K →
      ∀ (args rets : List E) (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)) := by
    intro f hf K hK args rets L' hreg hpre
    cases Bd with
    | none => exact (kindD_holds hκ hK args rets L' hreg hpre).toO
    | some Bk =>
      exact ((kindDB (cert := cert) hκ (hTot Bk rfl f hf) hK args rets L' hreg
        hpre).toCompleteAtB).toO
  have hlp : ∀ e ∈ lpTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LpAtO fs cert κ e.1 e.2.2.1 e.2.1 e.2.2.2.1 e.2.2.2.2 (Bd.map (· e.1)) := by
    intro e he hn
    cases Bd with
    | none => exact lpAtO_of_D (level_positions_completeAt fs cert κ hrf hcons (by omega) e he)
    | some Bk => exact (hHB Bk rfl).1 e he _ (hTot Bk rfl _ hn)
  have hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2
        (Bd.map (· e.1)) := by
    intro e he hn
    cases Bd with
    | none => exact level_queries_completeAtOP fs cert κ e he
    | some Bk => exact (hHB Bk rfl).2.1 e he _ (hTot Bk rfl _ hn)
  have hlr : ∀ e ∈ lrTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LrAtO fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 (Bd.map (· e.1)) := by
    intro e he hn
    cases Bd with
    | none => exact lrAtO_of_D (hLR fs cert κ hrf hcons hκ e he)
    | some Bk => exact (hHB Bk rfl).2.2 e he _ (hTot Bk rfl _ hn)
  have hargs : (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur,
      tabs]).length = 11 := by simp [capOf]
  have h := arm_completeAtO (Bd := Bd) hm hri hf' hps hbody hnamed hlp hlq hlr hargs rfl H hLin
  have e : (Bd.map fun Bk ↦ osBos fs Bk (openName μ) (osCfgR m ri)) =
      Bd.map fun Bk ↦ osBosAt fs Bk μ := by
    cases Bd <;> simp [osBosAt, osBos_rate, m]
  rw [e] at h
  exact ⟨fn, hf', hbody, h⟩

/-- **`open_stacked` is complete placed at an optional words bound.** -/
theorem open_stacked_completeAtO_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec)
    {μ r : ℕ} (hμ1 : minOpenLog ≤ μ) (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {Bd : Option (String → ℕ)} (hleaf : ∀ Bk ∈ Bd, OsLeafBounds fs Bk)
    (hHB : ∀ Bk ∈ Bd, HelperBounds fs cert κ)
    {S : KeccakState} {root : Digest} {target cur tabs : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hnz : NoZeroChallenge μ r target S xs os root) (hcaps : CapsAgree μ r target S xs os root)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    CompleteAtO fs cert κ (openName μ) Lin
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
      (OsOut μ w) (Bd.map fun Bk ↦ osBosAt fs Bk μ) := by
  obtain ⟨H⟩ := hH μ r hμ1 hμ2 hr1 hr4 S root target cur tabs xs os w s' roots' hrun hnz hcaps
  obtain ⟨_, -, -, h⟩ := open_stacked_completeAtOT_of hLR hμ2 hr1 hr4 hrf hcons hκ hleaf hHB H hLin
  exact h.toO

/-- **`open_stacked` is complete placed at every stack log and rate**, given the body's honest
data and `level_residual`'s placed statement. -/
theorem open_stacked_completeAtD_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec) :
    open_stacked_completeAtD_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ hrf hcons hκ S root target cur tabs xs os w s' roots' hrun hnz
    hcaps Lin hLin
  exact (open_stacked_completeAtO_of (Bd := none) hH hLR hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun _ h ↦ absurd h (by simp)) (fun _ h ↦ absurd h (by simp)) hrun hnz hcaps hLin).toD

/-- **`open_stacked` is complete placed within `osBosAt` words**, given also the helpers within
the bounds of their trees. -/
theorem open_stacked_completeAtB_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec)
    (hHB : ∀ fs cert κ, Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → (∀ f, fs f < 2 ^ 32) →
      HelperBounds fs cert κ) :
    open_stacked_completeAtB_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ Bnd hrf hcons hκ hleaf hfs S root target cur tabs xs os w s'
    roots' hrun hnz hcaps Lin hLin
  exact (open_stacked_completeAtO_of (Bd := some Bnd) hH hLR hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun _ h ↦ by cases h; exact hleaf) (fun _ _ ↦ hHB fs cert κ hrf hcons hκ hfs) hrun hnz hcaps
    hLin).toB

end
end LeanVM.Guest.B1.Arm
