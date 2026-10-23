/-
  LeanVM.Guest.B1.Whir.OsLay

  A configuration's buffer layout: its levels' windows disjoint and inside their buffers.
-/

module

public import LeanVM.Guest.B1.Whir.OsCont

/-!
# The layout (TRIAGE #36)

`OsLayoutOk cfg`: each buffer holding one window per level holds them in order, each inside it,
and the levels' own buffers hold their words (decided per configuration). `os_segDisj_range`:
windows in order are disjoint; `os_own_fits`: the honest words fit the buffers' sizes.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A configuration's layout.** -/
structure OsLayoutOk (cfg : OsCfg) : Prop where
  caps : ∀ i j, i < j → j < cfg.levels.length →
    4 * (cfg.lv i).capOff + 2 * 2 ^ ((cfg.lv i).capDepth + 1) ≤ 4 * (cfg.lv j).capOff
  capsFit : ∀ i < cfg.levels.length, 4 * (cfg.lv i).capOff + 2 * 2 ^ ((cfg.lv i).capDepth + 1) ≤ 4 * cfg.capLen
  flags : ∀ i j, i < j → j < cfg.levels.length → (cfg.lv i).capOff + 2 ^ (cfg.lv i).capDepth ≤ (cfg.lv j).capOff
  flagsFit : ∀ i < cfg.levels.length, (cfg.lv i).capOff + 2 ^ (cfg.lv i).capDepth ≤ cfg.capLen
  fch : ∀ i j, i < j → j < cfg.levels.length → (cfg.lv i).foldsOff + (cfg.lv i).folds ≤ (cfg.lv j).foldsOff
  fchFit : ∀ i < cfg.levels.length, (cfg.lv i).foldsOff + (cfg.lv i).folds ≤ cfg.nFolds
  qw : ∀ i < cfg.levels.length, (cfg.lv i).queries ≤ cfg.maxQ
  pos : ∀ i j, i < j → j < cfg.levels.length →
    (cfg.lv i).posOff + (cfg.lv i).squeezes * (192 / (cfg.lv i).depth) ≤ (cfg.lv j).posOff
  posFit : ∀ i < cfg.levels.length, (cfg.lv i).posOff + (cfg.lv i).squeezes * (192 / (cfg.lv i).depth) ≤ cfg.posLen
  cols : ∀ i < cfg.levels.length, (cfg.lv i).logCols ≤ 22
  basis : ∀ i < cfg.levels.length, (cfg.lv i).prefixLen + cfg.yrLog ≤ 22
  sq : ∀ i < cfg.levels.length, (cfg.lv i).squeezes ≤ cfg.maxSq
  il : ∀ i < cfg.levels.length, 2 ^ (cfg.lv i).folds ≤ cfg.maxIl
  queries : ∀ i < cfg.levels.length, 0 < (cfg.lv i).queries

/-- **Windows in order are disjoint.** -/
theorem os_segDisj_range {n : ℕ} (off : ℕ → ℕ) (c : ℕ → List E)
    (h : ∀ i j, i < j → j < n → off i + (c i).length ≤ off j) :
    OsSegDisj ((List.range n).map fun l => (off l, c l)) := by
  unfold OsSegDisj
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp_of_mem fun hi hj hij =>
    Or.inl (h _ _ hij (List.mem_range.mp hj))

theorem os_seg_mem {n : ℕ} {off : ℕ → ℕ} {c : ℕ → List E} {l : ℕ} (hl : l < n) :
    (off l, c l) ∈ (List.range n).map fun l => (off l, c l) :=
  List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩

private theorem os_forall₂_append {a b : List (List E)} {c d : List ℕ}
    (h1 : List.Forall₂ (fun c s => c.length ≤ s) a c) (h2 : List.Forall₂ (fun c s => c.length ≤ s) b d) :
    List.Forall₂ (fun c s => c.length ≤ s) (a ++ b) (c ++ d) := List.rel_append h1 h2

private theorem os_forall₂_range {f : ℕ → List (List E)} {g : ℕ → List ℕ} :
    ∀ n, (∀ l < n, List.Forall₂ (fun c s => c.length ≤ s) (f l) (g l)) →
      List.Forall₂ (fun c s => c.length ≤ s) ((List.range n).flatMap f) ((List.range n).flatMap g)
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append]
    exact os_forall₂_append (os_forall₂_range n fun l hl => h l (by omega)) (by simpa using h n (by omega))

/-- **The honest words fit the buffers.** -/
theorem os_own_fits {cfg : OsCfg} (hlay : OsLayoutOk cfg) (hyr5 : cfg.yrLog ≤ 5) {d : OsData} (hch : d.chst.length + 1 ≤ cfg.yrLog)
    {Q : List E} (hQ : Q.length ≤ cfg.posLen) (hfl : (d.fchC cfg).length ≤ cfg.nFolds) :
    List.Forall₂ (fun c s => c.length ≤ s) (d.ownQ cfg Q) (osSizes cfg) := by
  have hseg : ∀ (sz : ℕ) (segs : List (ℕ × List E)), (osSegC sz segs).length ≤ sz := fun sz segs => by
    rw [os_length_segC]
  unfold OsData.ownQ osSizes
  refine os_forall₂_append (os_forall₂_append (os_forall₂_append ?_ ?_) ?_) ?_
  · simp only [osHeadSizes, OsData.capsC, OsData.flagsC, OsData.rootsC, OsData.qwC, OsData.qposC,
      OsData.oodzC, OsData.oodC, OsData.betasC, OsData.fmsgC, osHMs]
    refine .cons (hseg _ _) (.cons (hseg _ _) (.cons ?_ (.cons (hseg _ _) (.cons hfl (.cons ?_
      (.cons (hseg _ _) (.cons (hseg _ _) (.cons hQ (.cons (hseg _ _) (.cons (hseg _ _) .nil))))))))))
    · simp
    · simp
  · rw [show (List.range cfg.levels.length).flatMap (fun _ => [2 * (cfg.maxSq + 1), cfg.maxIl]) =
        (List.range cfg.levels.length).flatMap (fun l => [2 * (cfg.maxSq + 1), cfg.maxIl]) from rfl]
    refine os_forall₂_range _ fun l hl => .cons ?_ (.cons ?_ .nil)
    · simp only [OsData.sqzC, List.length_flatMap, List.length_cons, List.length_nil, List.map_const',
        List.length_range, List.sum_replicate, smul_eq_mul]
      have := hlay.sq l hl; omega
    · simp [OsData.rewC]; exact hlay.il l hl
  · refine .cons ?_ (.cons (by simp [OsData.ptC]) (.cons (hseg _ _) (.cons (hseg _ _)
      (.cons (by simp [OsData.ichC]) .nil))))
    simp [OsData.tchC, OsData.tf]; omega
  · rw [show List.replicate cfg.levels.length (cfg.maxQ + 1) =
        (List.range cfg.levels.length).map (fun _ => cfg.maxQ + 1) by simp [List.map_const']]
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr fun l hl => ?_
    simp only [OsData.chvC, List.length_map, List.length_range]
    have := hlay.qw l (List.mem_range.mp hl); omega

end
end LeanVM.Guest.B1
