/-
  LeanVM.Guest.B1.Whir.OsPoint

  `open_stacked`'s point buffer's honest words are the opening's rotated point, zero-padded.
-/

module

public import LeanVM.Guest.B1.Whir.OsGlue

/-!
# The point (TRIAGE #36)

`OsData.ptC_eq`: the point's words read from the fold and tail challenges (`osPtSrc`) are the
challenges rotated by the first level's folds, then zeros.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

namespace OsData

variable {cfg : OsCfg} {d : OsData}

private theorem getD_append_l {l l' : List E} {i : ℕ} (h : i < l.length) : (l ++ l').getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem getD_append_r {l l' : List E} {i : ℕ} (h : l.length ≤ i) :
    (l ++ l').getD i 0 = l'.getD (i - l.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

private theorem getD_drop {l : List E} {k i : ℕ} : (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

private theorem getD_take {l : List E} {k i : ℕ} (h : i < k) : (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

/-- **The point's words.** -/
theorem ptC_eq (hS : (d.fchC cfg).length = cfg.nFolds) (hT : d.tf.length = cfg.yrLog)
    (hlane : (cfg.levels.headD default).folds ≤ cfg.nFolds) (h42 : cfg.nFolds + cfg.yrLog ≤ 42)
    (htne : OsRun.tch cfg ≠ osFch) :
    d.ptC cfg = ((d.fchC cfg ++ d.tf).drop (cfg.levels.headD default).folds ++
      (d.fchC cfg ++ d.tf).take (cfg.levels.headD default).folds) ++
      List.replicate (42 - (cfg.nFolds + cfg.yrLog)) 0 := by
  set S := d.fchC cfg
  set T := d.tf
  set lane := (cfg.levels.headD default).folds
  set nF := cfg.nFolds
  set yr := cfg.yrLog
  have hST : (S ++ T).length = nF + yr := by simp [hS, hT]
  apply List.ext_getElem (by simp [ptC, hST]; omega)
  intro i h1 h2
  have hi : i < 42 := by simpa [ptC] using h1
  rw [← List.getD_eq_getElem _ 0 h1, ← List.getD_eq_getElem _ 0 h2]
  simp only [ptC, os_getD_map_range _ hi, ent]
  have htch : ∀ o < yr, d.srcVal cfg (OsRun.tch cfg, o) = T.getD o 0 := fun o ho => by
    unfold srcVal; rw [ite_neg' htne]; simp only [tchC]; rw [getD_append_l (by rw [hT]; exact ho)]
  have hfch : ∀ o, d.srcVal cfg (osFch, o) = S.getD o 0 := fun o => by unfold srcVal; rw [ite_pos' rfl]
  have hdl : ((S ++ T).drop lane).length = nF + yr - lane := by simp [hST]
  have htl : ((S ++ T).take lane).length = lane := by simp [hST]; omega
  unfold osPtSrc
  by_cases c1 : i < nF - lane
  · rw [ite_pos' c1]; simp only
    rw [hfch, getD_append_l (by rw [List.length_append, hdl, htl]; omega), getD_append_l (by rw [hdl]; omega),
      getD_drop, getD_append_l (by omega)]
  · rw [ite_neg' c1]
    by_cases c2 : i < nF - lane + yr
    · rw [ite_pos' c2]; simp only
      rw [htch _ (by omega), getD_append_l (by rw [List.length_append, hdl, htl]; omega),
        getD_append_l (by rw [hdl]; omega), getD_drop, getD_append_r (by omega)]
      congr 1; omega
    · rw [ite_neg' c2]
      by_cases c3 : i < nF + yr
      · rw [ite_pos' c3]; simp only
        rw [hfch, getD_append_l (by rw [List.length_append, hdl, htl]; omega), getD_append_r (by rw [hdl]; omega),
          hdl, getD_take (by omega), getD_append_l (by omega)]
        congr 1; omega
      · rw [ite_neg' c3]; simp only
        rw [getD_append_r (by rw [List.length_append, hdl, htl]; omega), List.length_append, hdl, htl,
          List.getD_eq_getElem?_getD, List.getElem?_replicate, ite_pos' (by omega)]
        rfl

end OsData

end
end LeanVM.Guest.B1
