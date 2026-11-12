/-
  LeanVM.Guest.B1.Whir.CHonFields5

  OsHonest's `static` field: each level's `opening_queries` witnesses on the honest run.
-/

module

public import LeanVM.Guest.B1.Whir.CHonFields4
public import LeanVM.Guest.B1.Whir.HsScale

/-!
# The queries' static facts

`HonRun.finFold`: at the final level, each query's fold is the final polynomial's normalized
evaluation (`FinOk.req` with `novelSum_eq_novelEval`). `HonRun.fld_static`: OsHonest's `static`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem word0_ofK (n : ℕ) : word n 0 = ofK (K.ofBits n) := by
  simp only [word, Value.ofBits_zero]
  exact (ofK_eq_ofLimbs _).symm

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **The final level's folds are the final polynomial's normalized evaluations.** -/
theorem finFold : ∀ k < ((Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).qs μ).length,
    foldRow (lanesOf (oqSA (osCfgR (μ - minOpenLog) (r - 1)) (osCfgR (μ - minOpenLog) (r - 1)).yrLevel).base
        (((Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).phase.map (·.leaf)).getD k []))
      (K.ofBits (((Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).qs μ).getD k 0))
      (Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).rounds =
    novelSum (hdOf μ r Ls).hsFC
      (wsChain ((oqSA (osCfgR (μ - minOpenLog) (r - 1)) (osCfgR (μ - minOpenLog) (r - 1)).yrLevel).vs.map K.ofBits)
        (eOfNat (((Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default).qs μ).getD k 0)))
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) (osCfgR (μ - minOpenLog) (r - 1)).yrLevel).nHs
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) (osCfgR (μ - minOpenLog) (r - 1)).yrLevel).hsBits := by
  intro k hk
  have hy := hR.yr
  have hm := hR.m11
  have hyl : (osCfgR (μ - minOpenLog) (r - 1)).yrLevel < osNLevels (μ - minOpenLog) := by
    rw [← osCfgR_len _ (r - 1)]; omega
  have hB := hR.lvb (l := (osCfgR (μ - minOpenLog) (r - 1)).yrLevel) (by omega)
  obtain ⟨-, -, hbase, -, -, -, -, -⟩ := hB.qsh
  obtain ⟨-, -, -, hylen, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnHs, hhsb, hvs, h64, hle, hlc, -⟩ :=
    hR.fin
  obtain ⟨rw, W, hd, -, -, -, -, hfin, -⟩ := hR.last
  set L := Ls.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default with hL
  set lv := (osCfgR (μ - minOpenLog) (r - 1)).levels.getD (osCfgR (μ - minOpenLog) (r - 1)).yrLevel default with hlv
  have hrw : L.rw = rw := by unfold LvAt.rw; rw [hd]
  have hfw : L.fw = W := by unfold LvAt.fw; rw [hd]
  have hqs : L.qs μ = W.qs (rsF L.level L.cap rw)
      (μ - (rsSt L.level L.s L.cap rw).alphas.length + L.level.logInvRate) L.level.queries := by
    unfold LvAt.qs; rw [hd]; simp only [LvAt.F, LvAt.mu, LvAt.dp, LvAt.s1, hrw]
  have hph : L.phase = W.phase := by unfold LvAt.phase; rw [hd]
  have hrd : L.rounds = rsRounds L.level L.s L.cap rw := by simp only [LvAt.rounds, hrw]
  have hmu : μ - (rsSt L.level L.s L.cap rw).alphas.length = (osCfgR (μ - minOpenLog) (r - 1)).yrLog := by
    have := hB.mu
    simp only [LvAt.mu, LvAt.s1, hrw] at this
    rw [this, hlc]
  have hk' : k < (W.qs (rsF L.level L.cap rw)
      (μ - (rsSt L.level L.s L.cap rw).alphas.length + L.level.logInvRate) L.level.queries).length := by
    rw [← hqs]; exact hk
  have ho : k < W.phase.length := by rw [hfin.plen]; exact hk'
  have hreq := (hfin.req k hk' ho).trans
    (congrArg (fun m ↦ Verifier.novelEval W.fold (Verifier.subspaceAt m _)) hmu)
  -- the fold
  rw [hqs, hph, hrd, List.getD_eq_getElem _ _ hk', map_getD_eq _ _ _ ho, oqSA, oq_base, hbase,
    lanesOf_base, hreq]
  -- the final polynomial
  have hflen : W.fold.length = (osCfgR (μ - minOpenLog) (r - 1)).yrLen + lv.folds := by
    rw [hfin.flen, hmu, hylen, ← hB.fold]
  have hlv' : lv = osLvR (μ - minOpenLog) (r - 1) (osCfg (μ - minOpenLog)).yrLevel := osCfgR_getD hyl
  have hvan : vanishOk (osLvR (μ - minOpenLog) (r - 1) (osCfg (μ - minOpenLog)).yrLevel).vanish
      ((osLvR (μ - minOpenLog) (r - 1) (osCfg (μ - minOpenLog)).yrLevel).logCols + 1) = true :=
    vanish_allR (ri := r - 1) hm hyl
  rw [← hlv', hlc] at hvan
  rw [oq_vs, oq_nHs, oq_hsBits, hvs, hnHs, hhsb, ← hflen]
  refine (novelSum_eq_novelEval h64 _ _ (fun i hi ↦ ?_) W.fold (hdOf μ r Ls).hsFC (by rw [hflen]; exact hle)
    ?_ (fun c' hc ↦ ?_)).symm
  · rw [List.map_map, map_getD_eq _ _ _ (by simpa using hi), List.getElem_range, Function.comp_apply]
    exact vanish_val hvan i hi.le
  · simp only [OsHD.hsFC, List.length_map, List.length_range, hflen]
    rfl
  · have hc' : c' < (osCfgR (μ - minOpenLog) (r - 1)).yrLen + lv.folds := by rw [← hflen]; exact hc
    simp only [OsHD.hsFC]
    rw [map_getD_eq _ _ _ (by simp only [List.length_range]; exact hc'), List.getElem_range, word0_ofK]
    obtain ⟨rf1, rf2, -⟩ := osLvR_rateFree (μ - minOpenLog) (r - 1) (osCfg (μ - minOpenLog)).yrLevel
    have hs := hsScale_final hm (c := c') (by rw [osLvFin, ← rf1, ← hlv']; exact hc')
    rw [osLvFin, ← rf2, ← hlv'] at hs
    show (hdOf μ r Ls).Lf.fw.fold.getD c' 0 * ofK (K.ofBits (hsScale lv.vanish
      ((osCfg (μ - minOpenLog)).yrLog + 1) c' 1)) = _
    rw [hs]
    show L.fw.fold.getD c' 0 * _ = _
    rw [hfw]
    rfl

/-- **OsHonest's `static`.** -/
theorem fld_static : ∀ l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length,
    OqStatic (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l) (Ls.getD l default).rounds
      (if l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel then (hdOf μ r Ls).hsFC else [])
      (fun k ↦ ((Ls.getD l default).qs μ).getD k 0)
      (fun k ↦ ((Ls.getD l default).phase.map (·.leaf)).getD k [])
      (fun k ↦ ((Ls.getD l default).phase.map (fun o ↦ o.path.take ((((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).depth -
        (((osCfgR (μ - minOpenLog) (r - 1)).levels.getD l default)).capDepth))).getD k []) (oqQA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
  intro l hl k hk
  have hy := hR.yr
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  obtain ⟨-, -, hbase, hfolds, -, -, hfinal, -⟩ := (hR.lvb hl).qsh
  obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
  have hk' : k < qs.length := by rw [← hq]; omega
  have ho : k < ph.length := by omega
  obtain ⟨hw, hpl, -⟩ := openOne_facts (hok k hk' ho)
  have hmem : ((Ls.getD l default).qs μ).getD k 0 ∈ (Ls.getD l default).qs μ := by
    rw [hq, List.getD_eq_getElem _ _ hk']; exact List.getElem_mem hk'
  refine ⟨?_, ?_, ?_, fun hf ↦ ?_⟩
  · show _ < _
    rw [hpd, hcdq, Nat.sub_add_cancel hcdd]
    exact hR.qs_lt hl _ hmem
  · show (((Ls.getD l default).phase.map (·.leaf)).getD k []).length = _
    rw [hp, map_getD_eq _ _ _ ho, hw, oqSA, oq_base, oq_folds, hbase, hfolds]
    rfl
  · show (((Ls.getD l default).phase.map _).getD k []).length = _
    rw [hp, map_getD_eq _ _ _ ho, List.length_take, hpl, hpd]
    omega
  · rw [oqSA, oq_final, hfinal] at hf
    have he : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by
      by_contra hne
      simp [hne] at hf
    subst he
    simp only [↓reduceIte]
    exact hR.finFold k (by omega)

end HonRun

end
end LeanVM.Guest.B1.Whir
