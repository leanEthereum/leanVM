/-
  LeanVM.Guest.B1.Whir.BrFin1

  The finish's point and basis rows from the buffers' honest words.
-/

module

public import LeanVM.Guest.B1.Whir.BrMemL

/-!
# The point and the basis rows

`fin_pt`: the point's entries, from `fold_challenges` and `tail_challenges` as `osPtSrc` names
them, the point buffers holding them. `fin_bases`: level `i`'s basis row's memory (`BasisMemP`) at
the soundness proof's choices (`βof`, `Xof` of the records).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier

@[expose] public section

variable {c : OsCfg} {tr : OsTr}

theorem rs_get (h : TrFit c tr) {i : ℕ} (hi : i < c.levels.length) :
    tr.rs.getD i default = recOf (tr.L i) := by
  rw [OsTr.rs, List.getD_eq_getElem _ _ (by simp [h.len, hi]), List.getElem_map, OsTr.L,
    List.getD_eq_getElem _ _ (by rw [h.len]; exact hi)]

theorem rec_F (h : TrFit c tr) {i : ℕ} (hi : i < c.levels.length) :
    (tr.rs.getD i default).F = (lvAt c i).foldsOff + (lvAt c i).folds := by
  rw [rs_get h hi]
  simp only [recOf, SpLv.ws1, List.length_append, h.off i hi, SpLv.chs_length, (h.fit i hi).fold]

theorem tailC_get (h : TrFit c tr) (hs : OsSizes c) {rd : Reader} {T : E}
    (hT : ReadsAt rd T (tailC tr.Lf tr.xsR)) {k : ℕ} (hk : k < c.yrLog) :
    LoadHolds rd T k (tr.Tc.getD k 0) := by
  have hl : (tailChs tr.Lf tr.xsR).length = c.yrLog := h.tcLen
  have := readsAt_get hT (k := k) (by simp [tailC, hl]; have := hs.yr; omega)
  rwa [tailC, List.getD_append _ _ _ _ (by rw [hl]; exact hk)] at this

theorem fch_get {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {k : ℕ} (hk : k < c.nFolds) :
    LoadHolds rd P.fch k (tr.Fall.getD k 0) := readsAt_map_range hm.fch hk

/-- The point's entries. -/
theorem point_getD {lane nF yr : ℕ} {F T : List E} (hF : F.length = nF) (hT : T.length = yr)
    (hl : lane ≤ nF) (j : ℕ) :
    ((F ++ T).drop lane ++ (F ++ T).take lane).getD j 0 =
      if j < nF - lane then F.getD (lane + j) 0
      else if j < nF - lane + yr then T.getD (j - (nF - lane)) 0
      else if j < nF + yr then F.getD (j - (nF - lane) - yr) 0 else 0 := by
  have hlen : ((F ++ T).drop lane).length = nF + yr - lane := by simp [hF, hT]
  split_ifs with h1 h2 h3
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_eq_getElem?_getD, List.getElem?_drop,
      List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD, hF]
    congr 1; omega
  · rw [List.getD_append_right _ _ _ _ (by omega), hlen, List.getD_eq_getElem?_getD,
      List.getElem?_take]
    simp only [show j - (nF + yr - lane) < lane by omega, ↓reduceIte]
    rw [List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    congr 1; omega
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [hF, hT]; omega)]; rfl

theorem point_length (tr : OsTr) (lane : ℕ) :
    (tr.point lane).length = tr.Fall.length + tr.Tc.length := by
  simp only [OsTr.point, List.length_append, List.length_drop, List.length_take]; omega

/-- **The point's entries**, from their sources, in the point buffers. -/
theorem fin_pt {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {T PT PT1 : E}
    (hT : ReadsAt rd T (tailC tr.Lf tr.xsR))
    (hPT : ReadsAt rd PT (ptC tr (c.levels.headD default).folds))
    (hPT1 : ReadsAt rd PT1 (pt1C tr (c.levels.headD default).folds)) :
    ∀ j < pointCap, PtSrcP rd P T c j ((ptC tr (c.levels.headD default).folds).getD j 0) ∧
      LoadHolds rd PT j ((ptC tr (c.levels.headD default).folds).getD j 0) ∧
      LoadHolds rd PT1 j (1 + (ptC tr (c.levels.headD default).folds).getD j 0) := by
  intro j hj
  set lane := (c.levels.headD default).folds with hlane
  have hFl := fall_length hF h
  have hTl := h.tcLen
  have hpl : (tr.point lane).length = c.nFolds + c.yrLog := by rw [point_length, hFl, hTl]
  have hmu := hF.mu40; have hmu' := hF.mu
  have hptl : (ptC tr lane).length = pointCap := by simp [ptC, hpl]; omega
  have hpt1l : (pt1C tr lane).length = pointCap := by simp [pt1C, hpl]; omega
  have hv : (ptC tr lane).getD j 0 = (tr.point lane).getD j 0 := by
    rw [ptC]
    by_cases hj' : j < (tr.point lane).length
    · rw [List.getD_append _ _ _ _ hj']
    · have h1 : j - (tr.point lane).length < pointCap - (tr.point lane).length := by omega
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_eq_getElem?_getD (l := tr.point lane), List.getElem?_eq_none (by omega)]
      simp
  have hv1 : (pt1C tr lane).getD j 0 = 1 + (ptC tr lane).getD j 0 := by
    rw [hv, pt1C]
    by_cases hj' : j < (tr.point lane).length
    · rw [List.getD_append _ _ _ _ (by simpa using hj'), List.getD_eq_getElem _ _ (by simpa using hj'),
        List.getElem_map, ← List.getD_eq_getElem _ 0]
    · have h1 : j - ((tr.point lane).map (1 + ·)).length < pointCap - (tr.point lane).length := by
        simp only [List.length_map]; omega
      rw [List.getD_append_right _ _ _ _ (by simpa using hj'),
        List.getD_eq_getElem?_getD (l := tr.point lane), List.getElem?_eq_none (by omega)]
      simp only [List.length_map] at h1
      simp [List.getD_eq_getElem?_getD, h1]
  refine ⟨?_, by have := readsAt_get hPT (k := j) (by omega); exact this,
    by rw [← hv1]; exact readsAt_get hPT1 (k := j) (by omega)⟩
  rw [hv, OsTr.point, point_getD hFl hTl hF.lane]
  unfold PtSrcP
  rw [← hlane]
  split_ifs with h1 h2 h3
  · exact fch_get hm (by omega)
  · exact tailC_get h hs hT (by omega)
  · exact fch_get hm (by omega)
  · rfl

/-- Level `i`'s coordinates' values. -/
theorem xof_getD {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    {i : ℕ} (hi : i < c.levels.length) (t : ℕ) :
    Xof tr.rs tr.Fall tr.Tc i t =
      if t < (lvAt c i).prefixLen then tr.Fall.getD ((lvAt c i).resFoldOff + t) 0
      else tr.Tc.getD (t - (lvAt c i).prefixLen) 0 := by
  have hst := hF.lv i hi
  have hFl := fall_length hF h
  have hpre : (lvAt c i).prefixLen = c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) := by
    have a := hst.pre; have b := hst.cols; have d := hst.le
    simp only [lvAt] at *; omega
  have hle : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := hst.le
  have hrfo : (lvAt c i).resFoldOff = (lvAt c i).foldsOff + (lvAt c i).folds := hst.rfo
  unfold Xof
  rw [rec_F h hi]
  have hdl : (tr.Fall.drop ((lvAt c i).foldsOff + (lvAt c i).folds)).length =
      c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) := by rw [List.length_drop, hFl]
  split_ifs with h1
  · rw [List.getD_append _ _ _ _ (by rw [hdl]; omega), List.getD_eq_getElem?_getD,
      List.getElem?_drop, ← List.getD_eq_getElem?_getD, hrfo]
  · rw [List.getD_append_right _ _ _ _ (by rw [hdl]; omega), hdl, hpre]

theorem xof_ne {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    {i : ℕ} (hi : i < c.levels.length) {t : ℕ} (ht : t < (lvAt c i).logCols) :
    Xof tr.rs tr.Fall tr.Tc i t ≠ 0 := by
  have hst := hF.lv i hi
  have hFl := fall_length hF h
  have hTl := h.tcLen
  have hpre : (lvAt c i).prefixLen = c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) := by
    have a := hst.pre; have b := hst.cols; have d := hst.le
    simp only [lvAt] at *; omega
  have hcols : c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) + c.yrLog = (lvAt c i).logCols :=
    hst.cols
  have hrfo : (lvAt c i).resFoldOff = (lvAt c i).foldsOff + (lvAt c i).folds := hst.rfo
  rw [xof_getD hF h hi t]
  split_ifs with h1
  · rw [List.getD_eq_getElem _ _ (by rw [hFl]; omega)]
    exact h.fallNz _ (List.getElem_mem _)
  · rw [List.getD_eq_getElem _ _ (by rw [hTl]; omega)]
    exact h.tcNz _ (List.getElem_mem _)

/-- **Level `i`'s basis row's memory.** -/
theorem fin_bases {μ r : ℕ} {cfg : List Whir.Level} (hF : CandFacts c μ r cfg) (h : TrFit c tr)
    (hs : OsSizes c) {rd : Reader} {P : OsPtrs} (hm : FixedMem rd P c tr) {T BD LS : E}
    (hT : ReadsAt rd T (tailC tr.Lf tr.xsR)) (hBD : ReadsAt rd BD (bdC c tr))
    (hLS : ReadsAt rd LS (lsC c tr)) {i : ℕ} (hi : i < c.levels.length) :
    BasisMemP rd P T BD LS c i c.levels[i] (finB c tr i) (Xof tr.rs tr.Fall tr.Tc i) := by
  have hst := hF.lv i hi
  have hg : c.levels[i] = lvAt c i := (List.getD_eq_getElem _ _ hi).symm
  rw [hg]
  have hpl : (lvAt c i).prefixLen + c.yrLog = (lvAt c i).logCols := hst.pre
  have hcols : c.nFolds - ((lvAt c i).foldsOff + (lvAt c i).folds) + c.yrLog = (lvAt c i).logCols :=
    hst.cols
  have hle : (lvAt c i).foldsOff + (lvAt c i).folds ≤ c.nFolds := hst.le
  have hrfo : (lvAt c i).resFoldOff = (lvAt c i).foldsOff + (lvAt c i).folds := hst.rfo
  refine ⟨?_, fun t ht ↦ ⟨xof_ne hF h hi (by omega),
    (vanish_inv hst.vanish t (by simp only [lvAt] at *; omega)).2, ?_, ?_⟩, ?_⟩
  · have := readsAt_map_range hm.betas hi
    rw [finB, βof, Wof, rs_get h hi]
    simpa [recOf] using this
  · rw [xof_getD hF h hi t]
    unfold coordPtr coordSrc
    split_ifs with h1
    · exact fch_get hm (by omega)
    · exact tailC_get h hs hT (by omega)
  · have hc : (lvAt c i).logCols ≤ 22 := hs.cols i hi
    have := readsAt_map_range hBD (k := i * ligColsCap + t) (by simp only [ligColsCap]; nlinarith)
    simp only [ligColsCap] at this
    simp only [show (i * 22 + t) / 22 = i by omega, show (i * 22 + t) % 22 = t by omega, finD,
      dOf] at this
    exact this
  · have := readsAt_map_range hLS hi
    simpa [finL] using this

end
end LeanVM.Guest.B1.Whir
