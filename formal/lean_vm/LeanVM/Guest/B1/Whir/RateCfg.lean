/-
  LeanVM.Guest.B1.Whir.RateCfg

  A size's configuration at a rate: the body reads the levels' rate-free columns alone, so it is
  the body at the rate's levels; the dispatches on the rate's selector call the rate's
  specializations.
-/

module

public import LeanVM.Guest.B1.Whir.Flat

/-!
# A size's body at a rate

`open_stacked__L{m}` is `osBody (osCfg m)`, whose levels are the first rate's rows; the columns a
rate changes (`queries`, `depth`, `capDepth`, `squeezes`) reach the body only through
the dispatches' names (`OsCfg.lvAt`). So it is also the body at the configuration `osCfgR m ri`
whose levels are rate `ri`'s rows (`osBody_rate`), and the proof runs at that configuration.

* `OsLv.rf`: a row without the rate's columns; `osBody_rf`: the body of two configurations whose
  levels agree on the rest;
* `LvRate σ c lvl lv`: the selector `σ 0` is `g^ri` for a rate `ri < 4` whose row of level `lvl`
  is `lv`; `dispatch_rate`: a dispatch on it over `(c.lvAt lvl).map f` calls `f lv`.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1
open LeanVM.Guest.Value

@[expose] public section

/-- A level's row without the columns a rate changes. -/
def OsLv.rf (lv : OsLv) : OsLv :=
  { lv with queries := 0, depth := 0, capDepth := 0, squeezes := 0 }
/-- The configuration with the levels `L`. -/
abbrev OsCfg.withLevels (c : OsCfg) (L : List OsLv) : OsCfg := { c with levels := L }

theorem osLevel_cfg (c : OsCfg) (X : List OsLv) (lvl : Nat) (lv : OsLv) (st : OsSt) :
    osLevel c lvl lv st = osLevel (c.withLevels X) lvl lv st := rfl
theorem osLevel_rf (c : OsCfg) (lvl : Nat) (lv : OsLv) (st : OsSt) :
    osLevel c lvl lv st = osLevel c lvl lv.rf st := rfl

theorem osLevels_rf (c : OsCfg) (X : List OsLv) : ∀ (L L' : List OsLv), L.map OsLv.rf = L'.map OsLv.rf →
    ∀ lvl st, osLevels c lvl L st = osLevels (c.withLevels X) lvl L' st
  | [], [], _, _, _ => rfl
  | lv :: L, lv' :: L', h, lvl, st => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e : osLevel c lvl lv st = osLevel (c.withLevels X) lvl lv' st := by
      rw [osLevel_rf, h.1, ← osLevel_rf, osLevel_cfg c X]
    simp only [osLevels, e, osLevels_rf c X L L' h.2]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem osBasisRow_cfg (c : OsCfg) (X : List OsLv) bd tch lvl (lv : OsLv) k :
    osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1) =
      osBasisRow bd (osBasisCoords (c.withLevels X) tch lvl lv) k (k + 1) := rfl
theorem osBasisRow_rf (c : OsCfg) bd tch lvl (lv : OsLv) k :
    osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1) =
      osBasisRow bd (osBasisCoords c tch lvl lv.rf) k (k + 1) := rfl

theorem osBases_rf (c : OsCfg) (X : List OsLv) tch bd ls : ∀ (L L' : List OsLv),
    L.map OsLv.rf = L'.map OsLv.rf →
    ∀ lvl k, osBases c tch bd ls lvl L k = osBases (c.withLevels X) tch bd ls lvl L' k
  | [], [], _, _, _ => rfl
  | lv :: L, lv' :: L', h, lvl, k => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e : osBasisRow bd (osBasisCoords c tch lvl lv) k (k + 1) =
        osBasisRow bd (osBasisCoords (c.withLevels X) tch lvl lv') k (k + 1) := by
      rw [osBasisRow_rf, h.1, ← osBasisRow_rf, osBasisRow_cfg c X]
    simp only [osBases, e, osBases_rf c X tch bd ls L L' h.2]
  | [], _ :: _, h, _, _ => by simp at h
  | _ :: _, [], h, _, _ => by simp at h

theorem osResidual_cfg (c : OsCfg) (X : List OsLv) ich bd ls lvl (lv : OsLv) mats k :
    osResidual c ich bd ls lvl lv mats k = osResidual (c.withLevels X) ich bd ls lvl lv mats k := rfl
theorem osResidual_rf (c : OsCfg) ich bd ls lvl (lv : OsLv) mats k :
    osResidual c ich bd ls lvl lv mats k = osResidual c ich bd ls lvl lv.rf mats k := rfl

theorem osResiduals_rf (c : OsCfg) (X : List OsLv) ich bd ls : ∀ (L L' : List OsLv),
    L.map OsLv.rf = L'.map OsLv.rf →
    ∀ lvl mats k, osResiduals c ich bd ls lvl L mats k = osResiduals (c.withLevels X) ich bd ls lvl L' mats k
  | [], [], _, _, _, _ => rfl
  | lv :: L, lv' :: L', h, lvl, mats, k => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e : osResidual c ich bd ls lvl lv mats k = osResidual (c.withLevels X) ich bd ls lvl lv' mats k := by
      rw [osResidual_rf, h.1, ← osResidual_rf, osResidual_cfg c X]
    simp only [osResiduals, e, osResiduals_rf c X ich bd ls L L' h.2]
  | [], _ :: _, h, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _ => by simp at h

theorem osOodWeight_cfg (c : OsCfg) (X : List OsLv) tch p ol (lv : OsLv) k :
    osOodWeight c tch p ol lv k = osOodWeight (c.withLevels X) tch p ol lv k := rfl
theorem osOodWeight_rf (c : OsCfg) tch p ol (lv : OsLv) k :
    osOodWeight c tch p ol lv k = osOodWeight c tch p ol lv.rf k := rfl

theorem osOodWeights_rf (c : OsCfg) (X : List OsLv) tch : ∀ (L L' : List OsLv),
    L.map OsLv.rf = L'.map OsLv.rf →
    ∀ p ol acc k, osOodWeights c tch p ol L acc k = osOodWeights (c.withLevels X) tch p ol L' acc k
  | [], [], _, _, _, _, _ => rfl
  | lv :: L, lv' :: L', h, p, ol, acc, k => by
    simp only [List.map_cons, List.cons.injEq] at h
    have e : osOodWeight c tch p ol lv k = osOodWeight (c.withLevels X) tch p ol lv' k := by
      rw [osOodWeight_rf, h.1, ← osOodWeight_rf, osOodWeight_cfg c X]
    have hl : lv.logCols = lv'.logCols := by have := congrArg OsLv.logCols h.1; exact this
    simp only [osOodWeights, e, hl, osOodWeights_rf c X tch L L' h.2]
  | [], _ :: _, h, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _ => by simp at h

theorem osTail_cfg (c : OsCfg) (X : List OsLv) st : osTail c st = osTail (c.withLevels X) st := rfl

theorem headD_rf {L L' : List OsLv} (h : L.map OsLv.rf = L'.map OsLv.rf) :
    (L.headD default).rf = (L'.headD default).rf := by
  cases L <;> cases L' <;> simp_all

theorem osPtBlks_rf (c : OsCfg) (X : List OsLv) (hf : (c.levels.headD default).folds = (X.headD default).folds)
    pt pt1 tch : ∀ n i k, osPtBlks c pt pt1 tch i n k = osPtBlks (c.withLevels X) pt pt1 tch i n k
  | 0, _, _ => rfl
  | n + 1, i, k => by
    have e : osPtSrc c tch i = osPtSrc (c.withLevels X) tch i := by
      simp only [osPtSrc, hf]
    simp only [osPtBlks, e, osPtBlks_rf c X hf pt pt1 tch n]

/-- **The body depends on the levels' rate-free columns alone.** -/
theorem osBody_rf (c : OsCfg) (X : List OsLv) (h : X.map OsLv.rf = c.levels.map OsLv.rf) :
    osBody c = osBody (c.withLevels X) := by
  have hlen : X.length = c.levels.length := by
    have := congrArg List.length h; simpa using this
  have hhd := headD_rf h.symm
  have hf : (c.levels.headD default).folds = (X.headD default).folds := by
    have := congrArg OsLv.folds hhd; exact this
  have hlc : (c.levels.headD default).logCols = (X.headD default).logCols := by
    have := congrArg OsLv.logCols hhd; exact this
  have htl : c.levels.tail.map OsLv.rf = X.tail.map OsLv.rf := by
    rw [List.map_tail, List.map_tail, h]
  have hH : osHead c = osHead (c.withLevels X) := by
    simp only [osHead, hlen]
  simp only [osBody, osFinish]
  rw [hH, osLevels_rf c X c.levels X h.symm, ← osTail_cfg c X]
  simp only [hlen, hlc, osPtBlks_rf c X hf, osBases_rf c X _ _ _ c.levels X h.symm,
    osResiduals_rf c X _ _ _ c.levels X h.symm, osOodWeights_rf c X _ c.levels.tail X.tail htl]

/-! ## A size at a rate -/

/-- Size `m`'s configuration with its levels at rate `ri`. -/
def osCfgR (m ri : ℕ) : OsCfg := (osCfg m).withLevels (osLevelsR m ri)

theorem osLevelsR_rf (m ri : ℕ) :
    (osLevelsR m ri).map OsLv.rf = (osCfg m).levels.map OsLv.rf := by
  simp only [osCfg, osLevelsR, List.map_map]
  exact List.map_congr_left fun _ _ ↦ rfl

/-- **A size's body is its body at any rate's levels.** -/
theorem osBody_rate (m ri : ℕ) : osBody (osCfg m) = osBody (osCfgR m ri) :=
  osBody_rf _ _ (osLevelsR_rf m ri)

theorem osCfgR_lvAt (m ri lvl : ℕ) : (osCfgR m ri).lvAt lvl = (osCfg m).lvAt lvl := rfl

theorem osCfgR_lvAt_length (m ri lvl : ℕ) : ((osCfgR m ri).lvAt lvl).length = 4 := by
  simp [osCfgR, OsCfg.lvAt, osCfg]

theorem osCfgR_lvAt_getD {m ri : ℕ} (lvl : ℕ) (hri : ri < 4) :
    ((osCfgR m ri).lvAt lvl).getD ri default = (osCfgR m ri).levels.getD lvl default := by
  simp only [osCfgR, OsCfg.lvAt, osCfg, OsCfg.withLevels]
  rw [List.getD_eq_getElem _ _ (by simpa using hri)]
  simp only [List.getElem_map, List.getElem_range]

/-! ## The dispatches -/

/-- The rate's selector at level `lvl`: `σ 0 = g^ri`, `ri < 4`, and rate `ri`'s row of the level
is `lv`. -/
def LvRate (σ : Val) (c : OsCfg) (lvl : ℕ) (lv : OsLv) : Prop :=
  ∃ ri < 4, σ (.n osRate) = ofK (addressOfIndex ri) ∧ (c.lvAt lvl).length = 4 ∧
    (c.lvAt lvl).getD ri default = lv

/-- **A dispatch on the rate's selector** over the names `f` gives the rate's rows calls `f lv`. -/
theorem dispatch_rate {C : CallRel} {rd : Reader} {σ : Val} {c : OsCfg} {lvl : ℕ} {lv : OsLv}
    (hr : LvRate σ c lvl lv) (f : OsLv → String) {args rets : List V}
    (h : StmtOk C rd σ (.dispatch (.n osRate) ((c.lvAt lvl).map f) args rets)) :
    C (f lv) (args.map σ) (rets.map σ) := by
  obtain ⟨ri, hri, hx, hlen, hlv⟩ := hr
  have := stmtOk_dispatch hx (by omega) (by simp [hlen]) h
  obtain ⟨hlt, hc⟩ := this
  rw [List.length_map] at hlt
  rwa [List.getD_eq_getElem _ _ (by simpa using hlt), List.getElem_map,
    ← List.getD_eq_getElem _ default hlt, hlv] at hc

end
end LeanVM.Guest.B1.Whir
