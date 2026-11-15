/-
  LeanVM.Guest.Backend.Complete.Tmps

  What `TmpsApart` says, unpacked: each temporary has a cell, no other named value is placed at a
  temporary's cell, and the placed body's instructions name each temporary's cell exactly once.
-/

module

public import LeanVM.Guest.Backend.Complete.Cells

namespace LeanVM.Guest.Backend.Complete

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

theorem fold_contains (locs : VMap Loc) (n : ℕ) (g : NMap Unit → V → NMap Unit)
    (hg : ∀ m t, (g m t).contains n = true ↔ m.contains n = true ∨ cellP locs t = some n) :
    ∀ (ts : List V) (m : NMap Unit),
      (ts.foldl g m).contains n = true ↔ m.contains n = true ∨ ∃ t ∈ ts, cellP locs t = some n
  | [], m => by simp
  | t :: ts, m => by
      rw [List.foldl_cons, fold_contains locs n g hg ts, hg]
      simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

/-- **The set of the temporaries' cells.** -/
theorem tmpCellSet_contains (locs : VMap Loc) (ts : List V) (n : ℕ) :
    (tmpCellSet locs ts).contains n = true ↔ ∃ t ∈ ts, cellP locs t = some n := by
  unfold tmpCellSet
  rw [fold_contains locs n _ ?_ ts {}]
  · simp [NMap.contains]
  · intro m t
    split
    · next k e =>
      rw [e]
      simp only [NMap.contains, NMap.get?_insert, Option.some.injEq]
      by_cases h : n = k
      · subst h; simp
      · simp [h, Ne.symm h]
    · next e =>
      simp only [e, reduceCtorEq, or_false]

theorem cellCounts_cells (set : NMap Unit) (n : ℕ) : ∀ (cs : List ℕ) (m : NMap ℕ),
    ((cs.foldl (fun m c => if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m)
      m).get? n).getD 0 = (m.get? n).getD 0 + (if set.contains n then cs.count n else 0)
  | [], m => by simp
  | c :: cs, m => by
      rw [List.foldl_cons, cellCounts_cells set n cs, List.count_cons]
      split
      · next hc =>
        rw [NMap.get?_insert]
        by_cases h : n = c
        · subst h; simp [hc]; omega
        · simp only [h, ↓reduceIte, beq_iff_eq]
          split <;> simp [Ne.symm h]
      · next hc =>
        by_cases h : n = c
        · subst h; simp [hc]
        · simp [Ne.symm h]

theorem cellCounts_go (set : NMap Unit) (n : ℕ) : ∀ (ops : List LOp) (m : NMap ℕ),
    ((ops.foldl (fun m o => (opCells o).foldl (fun m c =>
      if set.contains c then m.insert c ((m.get? c).getD 0 + 1) else m) m) m).get? n).getD 0 =
      (m.get? n).getD 0 + (if set.contains n then (ops.flatMap opCells).count n else 0)
  | [], m => by simp
  | o :: os, m => by
      rw [List.foldl_cons, cellCounts_go set n os, cellCounts_cells, List.flatMap_cons,
        List.count_append]
      split <;> omega

/-- **How many times the instructions name a cell of the set.** -/
theorem cellCounts_get (set : NMap Unit) (ops : List LOp) (n : ℕ) :
    ((cellCounts set ops).get? n).getD 0 =
      if set.contains n then (ops.flatMap opCells).count n else 0 := by
  rw [cellCounts, cellCounts_go]
  simp

variable {tf : TracedFn} {pf : Placed}

theorem TmpsApart.with (h : TmpsApart tf pf) :
    apartWith tf pf (Stmt.tmpsList tf.core.body) (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body))
      (cellCounts (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body)) (blockOps pf.fn.body 0)) =
      true := by
  unfold TmpsApart tmpsApartB at h
  rw [nmapSeq_eq, nmapSeq_eq, Bool.and_eq_true] at h
  exact h.2

/-- **A temporary has a cell.** -/
theorem TmpsApart.cell (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body) :
    ∃ n, cellP pf.locs t = some n := by
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  exact Option.isSome_iff_exists.mp (hw.1.1 t ht)

/-- **No value the body names or takes is placed at a temporary's cell.** -/
theorem TmpsApart.apart (h : TmpsApart tf pf) {v : V}
    (hv : v ∈ Stmt.usesList tf.core.body ++ tf.core.params) {l : Loc} (hl : pf.locs[v]? = some l)
    {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body) : cellP pf.locs t ≠ some (locBase l) := by
  intro he
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  have := hw.1.2 v hv
  rw [hl] at this
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
  have hc := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) (locBase l)).mpr ⟨t, ht, he⟩
  rw [this] at hc
  exact Bool.false_ne_true hc

/-- **The placed body's instructions name a temporary's cell exactly once.** -/
theorem TmpsApart.count (h : TmpsApart tf pf) {t : V} (ht : t ∈ Stmt.tmpsList tf.core.body)
    {n : ℕ} (hn : cellP pf.locs t = some n) :
    ((blockOps pf.fn.body 0).flatMap opCells).count n = 1 := by
  have hw := h.with
  simp only [apartWith, Bool.and_eq_true, List.all_eq_true] at hw
  have := hw.2 t ht
  rw [hn] at this
  have hs := (tmpCellSet_contains pf.locs (Stmt.tmpsList tf.core.body) n).mpr ⟨t, ht, hn⟩
  have hg := cellCounts_get (tmpCellSet pf.locs (Stmt.tmpsList tf.core.body))
    (blockOps pf.fn.body 0) n
  rw [beq_iff_eq.mp this, hs] at hg
  simpa using hg.symm

end
end LeanVM.Guest.Backend.Complete
