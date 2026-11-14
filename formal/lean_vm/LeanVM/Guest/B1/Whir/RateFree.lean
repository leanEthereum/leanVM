/-
  LeanVM.Guest.B1.Whir.RateFree

  `open_stacked`'s template reads its levels' rate-free columns alone, so a size's body is the same
  at every rate's levels.
-/

module

public import LeanVM.Guest.B1.Whir.Template

/-!
# The body reads the rate-free columns

A rate changes a level's `queries`, `depth`, `capDepth` and `squeezes`; the body reads them only
through the dispatches' names, which take every rate's rows (`OsCfg.lvAt`), never the levels'.
Each block at a configuration with any levels `L` (`OsCfg.withLevels`) and a level `lv` is the
block at `c` and the level's rate-free columns `lv.rf`; so is the body (`osBody_rf`), and a size's
body at rate `ri`'s levels is its body at the first rate's (`osBody_rate`), for every size and rate,
with no evaluation.
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- A level's rate-free columns, the rate's zeroed. -/
def OsLv.rf (lv : OsLv) : OsLv := { lv with queries := 0, depth := 0, capDepth := 0, squeezes := 0 }

namespace OsLv
variable (lv : OsLv)
@[simp] theorem rf_folds : lv.rf.folds = lv.folds := rfl
@[simp] theorem rf_foldsOff : lv.rf.foldsOff = lv.foldsOff := rfl
@[simp] theorem rf_leafCells : lv.rf.leafCells = lv.leafCells := rfl
@[simp] theorem rf_posOff : lv.rf.posOff = lv.posOff := rfl
@[simp] theorem rf_logCols : lv.rf.logCols = lv.logCols := rfl
@[simp] theorem rf_highBits : lv.rf.highBits = lv.highBits := rfl
@[simp] theorem rf_prefixLen : lv.rf.prefixLen = lv.prefixLen := rfl
@[simp] theorem rf_resFoldOff : lv.rf.resFoldOff = lv.resFoldOff := rfl
@[simp] theorem rf_vanish : lv.rf.vanish = lv.vanish := rfl
@[simp] theorem rf_rf : lv.rf.rf = lv.rf := rfl
end OsLv

variable (c : OsCfg) (L : List OsLv)

/-! ## The blocks -/

theorem osFinalMsg_wl (lv : OsLv) (s : OsSt) :
    osFinalMsg (c.withLevels L) lv s = osFinalMsg c lv.rf s := by
  dsimp only [osFinalMsg, OsCfg.withLevels, OsLv.rf_folds]

theorem osCommit_wl (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osCommit (c.withLevels L) lvl lv s = osCommit c lvl lv.rf s := by
  dsimp only [osCommit, OsCfg.withLevels, OsLv.rf_folds, OsLv.rf_logCols]

theorem osPositions_wl (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osPositions (c.withLevels L) lvl lv s = osPositions c lvl lv.rf s := by
  dsimp only [osPositions, OsCfg.withLevels, OsLv.rf_posOff, OsCfg.lvAt]

theorem osHsFinal_wl (lv : OsLv) (s : OsSt) :
    osHsFinal (c.withLevels L) lv s = osHsFinal c lv.rf s := by
  dsimp only [osHsFinal, OsCfg.withLevels, OsLv.rf_folds, OsLv.rf_vanish]

theorem osHsMid_rf (lvl : ℕ) (lv : OsLv) (s : OsSt) : osHsMid lvl lv s = osHsMid lvl lv.rf s := by
  dsimp only [osHsMid, OsLv.rf_folds, OsLv.rf_vanish, OsLv.rf_highBits, OsLv.rf_logCols]

theorem osQueriesName_wl : osQueriesName { c with levels := L } = osQueriesName c := rfl

theorem osQueries_wl (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osQueries (c.withLevels L) lvl lv s = osQueries c lvl lv.rf s := by
  dsimp only [osQueries, OsCfg.withLevels, OsLv.rf_foldsOff, OsLv.rf_posOff, OsCfg.lvAt, osQueriesName_wl]

theorem osLevel_wl (lvl : ℕ) (lv : OsLv) (s : OsSt) :
    osLevel (c.withLevels L) lvl lv s = osLevel c lvl lv.rf s := by
  simp only [osLevel, osFinalMsg_wl, osCommit_wl, osPositions_wl, osHsFinal_wl, osQueries_wl,
    OsLv.rf_folds, OsLv.rf_foldsOff, ← osHsMid_rf]

theorem osLevels_wl :
    ∀ (lvl : ℕ) (L' : List OsLv) (s : OsSt),
      osLevels (c.withLevels L) lvl L' s = osLevels c lvl (L'.map OsLv.rf) s
  | _, [], _ => rfl
  | lvl, lv :: L', s => by
    simp only [List.map_cons, osLevels, osLevel_wl, osLevels_wl lvl.succ L']

theorem osBases_wl (tch bd ls la : ℕ) :
    ∀ (lvl : ℕ) (L' : List OsLv) (k : ℕ),
      osBases (c.withLevels L) tch bd ls la lvl L' k = osBases c tch bd ls la lvl (L'.map OsLv.rf) k
  | _, [], _ => rfl
  | lvl, lv :: L', k => by
    have e : osBasisCoords (c.withLevels L) tch lvl lv = osBasisCoords c tch lvl lv.rf := by
      rfl
    simp only [List.map_cons, osBases, e, osBases_wl tch bd ls la lvl.succ L']

theorem osResiduals_wl (ich bd ls la : ℕ) :
    ∀ (lvl : ℕ) (L' : List OsLv) (mats : List OsMat) (k : ℕ),
      osResiduals (c.withLevels L) ich bd ls la lvl L' mats k =
        osResiduals c ich bd ls la lvl (L'.map OsLv.rf) mats k
  | _, [], _, _ => rfl
  | lvl, lv :: L', mats, k => by
    have e : osResidual (c.withLevels L) ich bd ls la lvl lv mats k =
        osResidual c ich bd ls la lvl lv.rf mats k := by
      dsimp only [osResidual, OsCfg.withLevels, OsLv.rf_posOff, OsCfg.lvAt]
    simp only [List.map_cons, osResiduals, e, osResiduals_wl ich bd ls la lvl.succ L']

theorem osOodWeights_wl (tch : ℕ) :
    ∀ (prevCols ol : ℕ) (L' : List OsLv) (acc : Option ℕ) (k : ℕ),
      osOodWeights (c.withLevels L) tch prevCols ol L' acc k =
        osOodWeights c tch prevCols ol (L'.map OsLv.rf) acc k
  | _, _, [], _, _ => rfl
  | prevCols, ol, lv :: L', acc, k => by
    have e : ∀ k, osOodWeight (c.withLevels L) tch prevCols ol lv k = osOodWeight c tch prevCols ol lv.rf k := by
      intro k
      dsimp only [osOodWeight, OsCfg.withLevels, OsLv.rf_foldsOff]
    simp only [List.map_cons, osOodWeights, e, OsLv.rf_logCols, osOodWeights_wl tch _ ol.succ L']

theorem osPtBlks_congr {c' : OsCfg} {tch : ℕ} (h : ∀ i, osPtSrc c tch i = osPtSrc c' tch i)
    (pt pt1 : ℕ) : ∀ (i n k : ℕ), osPtBlks c pt pt1 tch i n k = osPtBlks c' pt pt1 tch i n k
  | _, 0, _ => rfl
  | i, n + 1, k => by
    simp only [osPtBlks, h i, osPtBlks_congr h pt pt1 (i + 1) n]

/-! ## The body -/

theorem headD_rf (L : List OsLv) : (L.map OsLv.rf).headD default = (L.headD default).rf := by
  cases L <;> rfl

theorem getD_rf (L : List OsLv) (i : ℕ) : (L.map OsLv.rf).getD i default = (L.getD i default).rf := by
  induction L generalizing i with
  | nil => rfl
  | cons a L ih => cases i with
    | zero => rfl
    | succ n => exact ih n

/-- The body at the levels `L` is the body at their rate-free columns. -/
theorem osBody_wl : osBody (c.withLevels L) = osBody (c.withLevels (L.map OsLv.rf)) := by
  have hpt : ∀ tch i, osPtSrc (c.withLevels L) tch i = osPtSrc (c.withLevels (L.map OsLv.rf)) tch i := by
    intro tch i
    simp only [osPtSrc, headD_rf, OsLv.rf_folds]
  simp only [osBody, osHead, osTail, osFinish, osLevels_wl, osBases_wl, osResiduals_wl,
    osOodWeights_wl, osPtBlks_congr _ (hpt _), List.length_map, getD_rf, headD_rf, OsLv.rf_folds,
    OsLv.rf_logCols, ← List.map_take, ← List.map_tail, List.map_map]
  simp only [Function.comp_def, OsLv.rf_rf]

/-- **The body reads the levels' rate-free columns alone.** -/
theorem osBody_rf (L' : List OsLv) (h : L.map OsLv.rf = L'.map OsLv.rf) :
    osBody (c.withLevels L) = osBody (c.withLevels L') := by
  rw [osBody_wl, h, ← osBody_wl]

/-- **A size's body is its body at any rate's levels.** -/
theorem osBody_rate (m ri : ℕ) : osBody (osCfg m) = osBody (osCfgR m ri) :=
  osBody_rf (osCfg m) (osLevelsR m 0) (osLevelsR m ri) (by simp only [osLevelsR, List.map_map]; rfl)

end
end LeanVM.Guest.B1.Whir
