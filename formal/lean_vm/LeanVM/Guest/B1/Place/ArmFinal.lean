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
public import LeanVM.Guest.B1.Place.LpE
public import LeanVM.Guest.B1.Place.ArmNamedE
public import LeanVM.Guest.B1.Place.Ls

/-!
# `open_stacked`, placed, every arm

`HelperBounds`: each helper of the tables is complete placed within any bound of its valid trees (`TotalLe`),
`level_positions` exact (`LpAtOE`). `open_stacked_completeAtOT_of`: the arm of `μ`, called on the rate's selector, is
complete placed at an optional words bound (`osBosAt`) by its node, from `arm_completeAtO`, the body's honest data `H`,
the named callees (`kindD_holds`, or `kindDB` and `kindDBE` within `OsLeafBounds`), and the helpers
(`level_positions_completeAtE`, `level_queries_completeAtOP`, `level_residual`'s statement, or `HelperBounds`;
`level_residual_slow`'s statement);
`open_stacked_completeAtO_of` with `H` from `os_honest_Spec`. `open_stacked_completeAtD_of`,
`open_stacked_completeAtB_of`: the two statements of `Place/OsSpec`.
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
  (∀ e ∈ lpTable, ∀ S, 1 ≤ S → S ≤ 64 → ∀ B,
    TotalLeOn coreProgram fs e.1 (fun a ↦ a.getD 9 0 = ofK (addressOfIndex S)) (fun _ ↦ B) →
    LpAtOE fs cert κ e.1 e.2.1 S e.2.2.1 e.2.2.2 (some B)) ∧
  (∀ e ∈ lqTable, ∀ B, TotalLe coreProgram fs e.1 (fun _ ↦ B) →
    LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
      e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2 (some B)) ∧
  (∀ e ∈ lrTable, ∀ q, resBatch ≤ q → q ≤ 2 ^ 20 → ∀ B,
    TotalLeOn coreProgram fs e.1 (fun a ↦ a.getD 4 0 = ofK (addressOfIndex (q / resBatch)) ∧
      a.getD 5 0 = ofK (addressOfIndex (q % resBatch))) (fun _ ↦ B) →
    LrAtOq fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 q (some B))

/-- **Arm `m`'s callees' names**: a `level_residual` specialization is no `level_positions` one, and a named callee
or a `level_queries` specialization neither. -/
def NamesOk (m : ℕ) : Prop :=
  (∀ f ∈ osResNames m, f ∉ osPosNames m) ∧ (∀ f ∈ osCalleeNames (osCfg m),
    ((osKindOf f).isSome = true ∨ f ∈ lqTable.map Prod.fst) → f ∉ osPosNames m ∧ f ∉ osResNames m) ∧
  ∀ r < ligNRates, ∀ j < (osCfg m).yrLevel,
    osSlowName (osCfgR m r) (osLvR m r j) ∉ osPosNames m ∧ osSlowName (osCfgR m r) (osLvR m r j) ∉ osResNames m

set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2048 in
instance (m : ℕ) : Decidable (NamesOk m) := by unfold NamesOk; infer_instance

set_option maxRecDepth 100000 in
theorem namesOk_all : ∀ m < osArms, NamesOk m := by decide +kernel

theorem totalLeOn_mono {fs : String → ℕ} {f : String} {Pre Pre' : List E → Prop} {B : List E → ℕ}
    (h : TotalLeOn coreProgram fs f Pre B) (hp : ∀ a, Pre' a → Pre a) : TotalLeOn coreProgram fs f Pre' B :=
  fun rd t a r hn hp' hv hb ↦ h rd t a r hn (hp a hp') hv hb

/-- A callee no specialization of the positions or the residual: its bound on every argument. -/
theorem totalLe_of_free {fs : String → ℕ} {m : ℕ} {f : String} {B : List E → ℕ}
    (h : TotalLeOn coreProgram fs f (osArgsOk m f) B) (h1 : f ∉ osPosNames m) (h2 : f ∉ osResNames m) :
    TotalLe coreProgram fs f B := fun rd t a r hn hv hb ↦
  h rd t a r hn (by simp only [osArgsOk, h1, h2, ↓reduceIte]) hv hb

theorem osCalleeNames_rate {m ri : ℕ} :
    osCalleeNames (osCfgR m ri) = osCalleeNames (osCfg m) := by
  unfold osCalleeNames osCallees; rw [← osBody_rate m ri]

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **`open_stacked` is complete placed at an optional words bound by its node**, from the body's honest data `H`,
within each bound its levels' `level_queries` popping their honest entries. -/
theorem open_stacked_completeAtOT_of (hLR : level_residual_completeAt_Spec)
    (hLS : level_residual_slow_completeAt_Spec)
    {μ r : ℕ} (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {Bd : Option (String → ℕ)} (hleaf : ∀ Bk ∈ Bd, OsLeafBounds fs Bk)
    (hHB : ∀ Bk ∈ Bd, HelperBounds fs cert κ) (hfs : ∀ Bk ∈ Bd, ∀ f, fs f < 2 ^ 32)
    (htl : ∀ Bk ∈ Bd, ∀ f, fs (tailKey f) ≤ fs f)
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
          (fun σ ↦ σ (.n osRate) = ofK (addressOfIndex (r - 1)) ∧ WinEx (osBodyA (osCfgR (μ - minOpenLog) (r - 1))) σ)
          (armTs (Bd := Bd) H)) := by
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
  have hTotOn : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri),
      TotalLeOn coreProgram fs f (osArgsOk m f) (fun _ ↦ Bk f) :=
    fun Bk hBk f hf ↦ hleaf Bk hBk m hm f (by rwa [osCalleeNames_rate] at hf)
  obtain ⟨hNres, hNfree, hNslow⟩ := namesOk_all m hm
  have hTot0 : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri), f ∉ osPosNames m → f ∉ osResNames m →
      TotalLe coreProgram fs f (fun _ ↦ Bk f) :=
    fun Bk hBk f hf h1 h2 ↦ totalLe_of_free (hTotOn Bk hBk f hf) h1 h2
  have hTot : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri),
      ((osKindOf f).isSome = true ∨ f ∈ lqTable.map Prod.fst) → TotalLe coreProgram fs f (fun _ ↦ Bk f) :=
    fun Bk hBk f hf hk ↦
      have hf' : f ∈ osCalleeNames (osCfg m) := by rwa [osCalleeNames_rate] at hf
      hTot0 Bk hBk f hf (hNfree f hf' hk).1 (hNfree f hf' hk).2
  have hLv := armLv_ok hm hri
  have hlen : (osCfgR m ri).levels.length = osNLevels m := osCfgR_levels_length m ri
  have hrow : ∀ l < (osCfgR m ri).levels.length, osLvA (osCfgR m ri) l = osLvR m ri l := fun l hl ↦
    (osLvR_eq_getD (hlen ▸ hl)).symm
  have hnamed : ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K →
      ∀ (args rets : List E) (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtO fs cert κ f L' args (Returns rets) (Bd.map (· f)) := by
    intro f hf K hK args rets L' hreg hpre
    cases Bd with
    | none => exact (kindD_holds hK args rets L' hreg hpre).toO
    | some Bk =>
      exact ((kindDB (cert := cert) (hTot Bk rfl f hf (Or.inl (by rw [hK]; rfl))) hK args rets L' hreg
        hpre).toCompleteAtB).toO
  have hnamedT : ∀ Bk ∈ Bd, ∀ f ∈ osCalleeNames (osCfgR m ri), ∀ K, osKindOf f = some K →
      ∀ (args rets : List E) (L' : Layout), RegPtrs K.spec args (RegionL L') →
      (∀ rd, LowDef κ rd → MemL rd L' → K.Pre rd args rets) →
      CompleteAtDTBR fs cert κ f L' args (Returns rets) armXT (Bk f) :=
    fun Bk hBk f hf K hK args rets L' hreg hpre ↦
      kindDBE (hTot Bk hBk f hf (Or.inl (by rw [hK]; rfl))) hK args rets L' hreg hpre
  have hlp : ∀ l < (osCfgR m ri).levels.length, osPositionsName (osLvA (osCfgR m ri) l) ∈ osCalleeNames (osCfgR m ri) →
      LpAtOE fs cert κ (osPositionsName (osLvA (osCfgR m ri) l))
      (lpLoopA (osCfgR m ri) l) (osLvA (osCfgR m ri) l).squeezes (osLvA (osCfgR m ri) l).depth
      (osLvA (osCfgR m ri) l).capDepth (Bd.map (· (osPositionsName (osLvA (osCfgR m ri) l)))) := by
    intro l hl hn
    obtain ⟨he, -, -, -, -, -, hS1, hS64, -⟩ := hLv l hl
    cases Bd with
    | none => exact level_positions_completeAtE fs cert κ hrf hcons (by omega) _ he _ hS1 hS64
    | some Bk =>
      refine (hHB Bk rfl).1 _ he _ hS1 hS64 _ (totalLeOn_mono (hTotOn Bk rfl _ ?_) fun a ha ↦ ?_)
      · exact hn
      · have hmem : osPositionsName (osLvA (osCfgR m ri) l) ∈ osPosNames m := by
          rw [hrow l hl]
          exact List.mem_flatMap.mpr ⟨ri, List.mem_range.mpr (by unfold ligNRates; omega),
            List.mem_map.mpr ⟨l, List.mem_range.mpr (hlen ▸ hl), rfl⟩⟩
        simp only [osArgsOk, hmem, ↓reduceIte]
        exact ⟨ri, by unfold ligNRates; omega, l, hlen ▸ hl, by rw [hrow l hl], by rw [← hrow l hl]; exact ha⟩
  have hlq : ∀ e ∈ lqTable, e.1 ∈ osCalleeNames (osCfgR m ri) →
      LqAtOP fs cert κ e.1 e.2.1 e.2.2.1 e.2.2.2.1 e.2.2.2.2.1 e.2.2.2.2.2.1 e.2.2.2.2.2.2.1
        e.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.1 e.2.2.2.2.2.2.2.2.2.2
        (Bd.map (· e.1)) := by
    intro e he hn
    cases Bd with
    | none => exact level_queries_completeAtOP fs cert κ e he
    | some Bk => exact (hHB Bk rfl).2.1 e he _ (hTot Bk rfl _ hn (Or.inr (List.mem_map.mpr ⟨e, he, rfl⟩)))
  have hlr : ∀ j < (osCfgR m ri).yrLevel, osResidualName (osLvA (osCfgR m ri) j) ∈ osCalleeNames (osCfgR m ri) →
      LrAtOq fs cert κ (osResidualName (osLvA (osCfgR m ri) j))
      (osLvA (osCfgR m ri) j).logCols (osLvA (osCfgR m ri) j).folds (osLvA (osCfgR m ri) j).highBits
      (osLvA (osCfgR m ri) j).queries (Bd.map (· (osResidualName (osLvA (osCfgR m ri) j)))) := by
    intro j hj hn
    have hyr := (armBody_ok hm hri).2.2.2.2
    have hjl : j < (osCfgR m ri).levels.length := by omega
    obtain ⟨-, -, hlrE, -⟩ := hLv j hjl
    obtain ⟨he, hq1, hq2⟩ := hlrE hj
    cases Bd with
    | none => exact (lrAtO_of_D (hLR fs cert κ hrf hcons hκ _ he)).q hq1 hq2
    | some Bk =>
      refine (hHB Bk rfl).2.2 _ he _ hq1 hq2 _ (totalLeOn_mono (hTotOn Bk rfl _ ?_) fun a ha ↦ ?_)
      · exact hn
      · have hyrm : (osCfgR m ri).yrLevel = (osCfg m).yrLevel := rfl
        have hmem : osResidualName (osLvA (osCfgR m ri) j) ∈ osResNames m := by
          rw [hrow j hjl, osResidualName_rate]
          exact List.mem_map.mpr ⟨j, List.mem_range.mpr (hyrm ▸ hj), rfl⟩
        simp only [osArgsOk, hNres _ hmem, hmem, ↓reduceIte]
        exact ⟨ri, by unfold ligNRates; omega, j, hyrm ▸ hj, by rw [hrow j hjl, osResidualName_rate],
          by rw [← hrow j hjl]; exact ha.1, by rw [← hrow j hjl]; exact ha.2⟩
  have hls : ∀ j < (osCfgR m ri).yrLevel,
      osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j) ∈ osCalleeNames (osCfgR m ri) →
      LsAtO fs cert κ (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j)) (osLvA (osCfgR m ri) j).queries
        (osLvA (osCfgR m ri) j).prefixLen (osCfgR m ri).yrLog (osLvA (osCfgR m ri) j).vanish
        (Bd.map (· (osSlowName (osCfgR m ri) (osLvA (osCfgR m ri) j)))) := fun j hj hn ↦
    hLS fs cert κ hrf hcons hκ m hm ri hri j hj _ fun B hB ↦ by
      obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB
      have hjl : j < (osCfgR m ri).levels.length := by have := (armBody_ok hm hri).2.2.2.2; omega
      have hs := hNslow ri (by unfold ligNRates; omega) j hj
      rw [← hrow j hjl] at hs
      exact ⟨hfs Bk hBk, hTot0 Bk hBk _ hn hs.1 hs.2⟩
  have hargs : (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur,
      tabs]).length = 11 := by simp [capOf]
  have h := arm_completeAtO (Bd := Bd) hm hri hκ htl hf' hps hbody hnamed hnamedT hlp hlq hlr hls hargs rfl H hLin
  refine ⟨fn, hf', hbody, fun fp ↦ ?_⟩
  obtain ⟨n, Lown, rets, Lout, ho, hw, hd, hn, hr⟩ := h fp
  refine ⟨n, Lown, rets, Lout, ho, hw, hd, fun B hB ↦ ?_, hr⟩
  obtain ⟨Bk, hBk, rfl⟩ := Option.mem_map.mp hB
  exact le_trans (hn _ (Option.mem_map.mpr ⟨Bk, hBk, rfl⟩)) (osBos_le_osBosAt fs Bk μ (by unfold ligNRates; omega))

/-- **`open_stacked` is complete placed at an optional words bound.** -/
theorem open_stacked_completeAtO_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec)
    (hLS : level_residual_slow_completeAt_Spec)
    {μ r : ℕ} (hμ1 : minOpenLog ≤ μ) (hμ2 : μ ≤ 30) (hr1 : 1 ≤ r) (hr4 : r ≤ 4)
    (hrf : Lift.RunsFit fs cert) (hcons : RunsConsec cert) (hκ : 11 ≤ κ)
    {Bd : Option (String → ℕ)} (hleaf : ∀ Bk ∈ Bd, OsLeafBounds fs Bk)
    (hHB : ∀ Bk ∈ Bd, HelperBounds fs cert κ) (hfs : ∀ Bk ∈ Bd, ∀ f, fs f < 2 ^ 32)
    (htl : ∀ Bk ∈ Bd, ∀ f, fs (tailKey f) ≤ fs f)
    {S : KeccakState} {root : Digest} {target cur tabs : E} {xs : List E}
    {os : List (List Opening)} {w : WhirEnd} {s' : Fs} {roots' : List (Digest × ℕ × ℕ)}
    (hrun : RunsWith (whirOpen μ r target) ⟨capOf S, []⟩ xs os [(root, stackShape μ r)] w s' roots')
    (hcaps : CapsAgree μ r target S xs os root)
    {Lin : Layout} (hLin : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd cur xs ∧ WinTabs rd tabs) :
    CompleteAtO fs cert κ (openName μ) Lin
      (rateSel r :: capOf S ++ [target, (digestHalves root).1, (digestHalves root).2, cur, tabs])
      (OsOut μ w) (Bd.map fun Bk ↦ osBosAt fs Bk μ) := by
  obtain ⟨H⟩ := hH μ r hμ1 hμ2 hr1 hr4 S root target cur tabs xs os w s' roots' hrun hcaps
  obtain ⟨_, -, -, h⟩ := open_stacked_completeAtOT_of hLR hLS hμ2 hr1 hr4 hrf hcons hκ hleaf hHB hfs htl H hLin
  exact h.toO

/-- **`open_stacked` is complete placed at every stack log and rate**, given the body's honest
data and `level_residual`'s and `level_residual_slow`'s placed statements. -/
theorem open_stacked_completeAtD_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec)
    (hLS : level_residual_slow_completeAt_Spec) : open_stacked_completeAtD_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ hrf hcons hκ S root target cur tabs xs os w s' roots' hrun
    hcaps Lin hLin
  exact (open_stacked_completeAtO_of (Bd := none) hH hLR hLS hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun _ h ↦ absurd h (by simp)) (fun _ h ↦ absurd h (by simp)) (fun _ h ↦ absurd h (by simp))
    (fun _ h ↦ absurd h (by simp)) hrun hcaps hLin).toD

/-- **`open_stacked` is complete placed within `osBosAt` words**, given also the helpers within
the bounds of their trees. -/
theorem open_stacked_completeAtB_of (hH : os_honest_Spec) (hLR : level_residual_completeAt_Spec)
    (hLS : level_residual_slow_completeAt_Spec)
    (hHB : ∀ fs cert κ, Lift.RunsFit fs cert → RunsConsec cert → 11 ≤ κ → (∀ f, fs f < 2 ^ 32) →
      HelperBounds fs cert κ) :
    open_stacked_completeAtB_Spec := by
  intro μ r hμ1 hμ2 hr1 hr4 fs cert κ Bnd hrf hcons hκ hleaf hfs htl S root target cur tabs xs os w s'
    roots' hrun hcaps Lin hLin
  exact (open_stacked_completeAtO_of (Bd := some Bnd) hH hLR hLS hμ1 hμ2 hr1 hr4 hrf hcons hκ
    (fun _ h ↦ by cases h; exact hleaf) (fun _ _ ↦ hHB fs cert κ hrf hcons hκ hfs) (fun _ _ ↦ hfs)
    (fun _ _ ↦ htl) hrun hcaps hLin).toB

end
end LeanVM.Guest.B1.Arm
