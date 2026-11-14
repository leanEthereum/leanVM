/-
  LeanVM.Guest.B1.Merkle.LevelPopsP

  The entries `level_queries` pops at the honest data (`lqCapE`, `oqPops`) are a level's `Hints.levelHints`, stream by stream, when its queries are the phase's openings and its cap and flags the generator's.
-/

module

public import LeanVM.Guest.B1.Merkle.QueryPops
public import LeanVM.Guest.B1.Place.LqProofP

/-!
# A level's placed pops are the generator's

* `QD.rowVals_eq`: a query's row cells are `Hints.leafCells` of its row;
* `oqQE_eq_query`: a query's entries (`oqQE`) at an opening's witness are its `queryEntries`;
* `oqPops_eq_levelPushes`: the queries of a phase, in order, pop `levelPushes`;
* `lq_sameStreams`: `level_queries`' entries, the cap and flags the generator's, are `Hints.levelHints`', stream by stream.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- **A query's row cells are the generator's leaf cells.** -/
theorem QD.rowVals_eq (d : QD) {first : Bool} (hfirst : d.s.base = 1 ↔ first = true)
    (hrow : d.row.length = rowLen d.s.base d.s.folds) : d.rowVals = Hints.leafCells first d.row := by
  rw [QD.rowVals]
  by_cases hb : d.s.base = 1
  · have hf : first = true := hfirst.mp hb
    subst hf
    rw [Hints.leafCells, ite_eq_left rfl]
    rw [rowLen, ite_eq_left hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < d.row.length by simpa using h2)]
  · have hf : first = false := by cases first <;> simp_all
    subst hf
    rw [Hints.leafCells, ite_eq_right (by simp)]
    rw [rowLen, ite_eq_right hb] at hrow
    refine List.ext_getElem (by simp [Oq.I, hrow]) fun i h1 h2 => ?_
    simp [QD.cell, hb]

/-- **A query's entries at an opening's witness are the opening's**: its position the leaf index, its row the leaf,
its siblings the path's first `pd`. -/
theorem oqQE_eq_query (s : Oq) {first : Bool} (hfirst : s.base = 1 ↔ first = true) (o : Opening)
    (hrow : o.leaf.length = rowLen s.base s.folds) (hl : s.pd ≤ o.path.length) :
    oqQE s (o.leafIndex, o.leaf, o.path.take s.pd) = queryEntries first (s.pd + s.cd) s.pd o := by
  unfold oqQE
  rw [QD.rowVals_eq (oqQD s 0 true 0 0 0 [] [] (o.leafIndex, o.leaf, o.path.take s.pd)) hfirst hrow,
    WD.wpPops_eq ((oqQD s 0 true 0 0 0 [] [] (o.leafIndex, o.leaf, o.path.take s.pd)).wd 0) (D := s.pd + s.cd)
      (path := o.path) rfl (by simp only [QD.wd, oqQD]; omega) hl]
  rfl

theorem flatMap_range_length {α β : Type} (g : α → List β) : ∀ (l : List α) (f : ℕ → List β),
    (∀ k (hk : k < l.length), f k = g l[k]) → (List.range l.length).flatMap f = l.flatMap g
  | [], _, _ => rfl
  | a :: l, f, h => by
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_cons, List.flatMap_map,
      h 0 (by simp), flatMap_range_length g l (fun k => f (k + 1)) fun k hk => h (k + 1) (by simp [hk])]
    rfl

/-- **The queries of a phase, in order, pop its pushes.** -/
theorem oqPops_eq_levelPushes (s : Oq) {first : Bool} (hfirst : s.base = 1 ↔ first = true) {depth count : ℕ}
    (hdepth : depth = s.pd + s.cd) (hpd : depth - Hints.capDepthOf count depth = s.pd) {phase : List Opening}
    {W : ℕ → QW} (hW : ∀ k (hk : k < phase.length), W k = (phase[k].leafIndex, phase[k].leaf, phase[k].path.take s.pd))
    (hrow : ∀ o ∈ phase, o.leaf.length = rowLen s.base s.folds) (hl : ∀ o ∈ phase, s.pd ≤ o.path.length) :
    oqPops s W phase.length = levelPushes first depth count phase := by
  rw [oqPops, levelPushes, hpd, hdepth]
  refine flatMap_range_length _ phase _ fun k hk => ?_
  rw [hW k hk]
  exact oqQE_eq_query s hfirst _ (hrow _ (List.getElem_mem hk)) (hl _ (List.getElem_mem hk))

/-- **`level_queries`' entries are `Hints.levelHints`'**, stream by stream: its queries a phase's openings, its cap
and flags the generator's (`levelCapPushes`). -/
theorem lq_sameStreams (s : Oq) {first : Bool} (hfirst : s.base = 1 ↔ first = true) {depth count : ℕ}
    (hdepth : depth = s.pd + s.cd) (hpd : depth - Hints.capDepthOf count depth = s.pd) {phase : List Opening}
    {W : ℕ → QW} (hW : ∀ k (hk : k < phase.length), W k = (phase[k].leafIndex, phase[k].leaf, phase[k].path.take s.pd))
    (hrow : ∀ o ∈ phase, o.leaf.length = rowLen s.base s.folds) (hl : ∀ o ∈ phase, s.pd ≤ o.path.length)
    {capW flW : List E} (hcap : lqCapE capW flW = levelCapPushes depth count phase) :
    SameStreams (lqCapE capW flW ++ oqPops s W phase.length) (Hints.levelHints first depth count phase) := by
  rw [hcap, oqPops_eq_levelPushes s hfirst hdepth hpd hW hrow hl]
  exact level_sameStreams first depth count phase

end
end LeanVM.Guest.B1
