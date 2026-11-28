/-
  LeanVM.Protocol.Relation.Link.GroupFold

  The row side's fold (`rowSideOf`) in closed form: the pointer columns it counts, the
  certificate's weight and the ring pieces, as sums and lists over the tables' pointer columns.
-/

module

public import LeanVM.Protocol.Relation.Link.Fold
public import LeanVM.Protocol.Relation.Link.GroupPoly

/-!
# The row side's fold in closed form

Pointer column `k` of table `t` is the row side's column `qBase t + k` (`qBase`, the pointer
columns of the tables before `t`). `rowSideOf_closed`: after every table, the column count is
`qBase` of the table count, the certificate's weight is
`Σ_t Σ_k eq(q, qBase t + k)·corner_t·ω_t·ε_{qBase t + k}` and the pieces are one per pointer column
(`pieceAt`), table by table.
-/

namespace LeanVM.Protocol.Relation

open LeanVM.Parameters LeanVM.Protocol.Verifier LeanVM.Protocol.Link Finset

@[expose] public section

/-- Table `t`'s pointer columns. -/
def ptrsOf (layout : Layout) (t : ℕ) : List ℕ := (layout.tables.map (·.links.pointers)).getD t []

/-- The pointer columns of the tables before `t`. -/
def qBase (layout : Layout) (t : ℕ) : ℕ := ∑ t' ∈ range t, (ptrsOf layout t').length

/-- Table `t`'s log-height. -/
def heightOf (layout : Layout) (t : ℕ) : ℕ := layout.tableLogHeights.getD t 0

/-- Table `t`'s corner at the row point. -/
def cornerAt (layout : Layout) (chi : List E) (t : ℕ) : E :=
  prodE ((chi.drop (heightOf layout t)).map (1 + ·))

/-- Table `t`'s row weight `ω_t` at the row point. -/
def omegaOf (layout : Layout) (ch : LinkCh) (chi : List E) (t : ℕ) : E :=
  omegaAt (ch.theta.getD t 0) (ch.tau.take (heightOf layout t)) (chi.take (heightOf layout t))
    (layout.tableRows.getD t 0)

/-- The ring piece of table `t`'s pointer column `k`. -/
def pieceAt (layout : Layout) (chi eqQ : List E) (t k : ℕ) : RingPiece :=
  { placement := some ((layout.placements.getD (globalColumnBases.getD t 0 + (ptrsOf layout t).getD k 0)
      none).getD default)
    point := chi.take (heightOf layout t)
    scale := eqQ.getD (qBase layout t + k) 0 }

theorem qBase_succ (layout : Layout) (t : ℕ) :
    qBase layout (t + 1) = qBase layout t + (ptrsOf layout t).length := by
  simp [qBase, sum_range_succ]

section Fold

variable (layout : Layout) (ch : LinkCh) (a : IdxAt) (jump eqQ chi : List E)

/-- **One table's pointer columns**: the count, the certificate's weight and the pieces. -/
theorem ptrFold_closed (point : List E) (corner omega act sHat sNext : E) (table : Table) (t : ℕ)
    (col : ℕ → E) : ∀ (L : List (ℕ × ℕ)) (acc : LinkRowSide),
    (L.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) acc).q =
        acc.q + L.length ∧
    (L.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) acc).certWeight =
        acc.certWeight + ∑ j ∈ range L.length,
          eqQ.getD (acc.q + j) 0 * corner * omega * ch.eps.getD (acc.q + j) 0 ∧
    (L.foldl (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col) acc).pieces =
        acc.pieces ++ (List.range L.length).map fun j ↦
          { placement := some ((layout.placements.getD (globalColumnBases.getD t 0 + (L.getD j (0, 0)).1)
              none).getD default)
            point := point
            scale := eqQ.getD (acc.q + j) 0 }
  | [], acc => by simp
  | (ptr, k) :: L, acc => by
    obtain ⟨h1, h2, h3⟩ := ptrFold_closed point corner omega act sHat sNext table t col L
      (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (ptr, k))
    have hq : (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (ptr, k)).q =
        acc.q + 1 := by simp [ptrStep]
    have hcw : (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc
        (ptr, k)).certWeight = acc.certWeight + eqQ.getD acc.q 0 * corner * omega * ch.eps.getD acc.q 0 := by
      simp [ptrStep]
    have hp : (ptrStep layout ch a eqQ point corner omega act sHat sNext table t col acc (ptr, k)).pieces =
        acc.pieces ++ [{ placement := some ((layout.placements.getD (globalColumnBases.getD t 0 + ptr)
          none).getD default), point := point, scale := eqQ.getD acc.q 0 }] := by
      simp [ptrStep]
    rw [List.foldl_cons]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, hq, List.length_cons]; omega
    · have hs : ∑ j ∈ range L.length, eqQ.getD (acc.q + 1 + j) 0 * corner * omega *
          ch.eps.getD (acc.q + 1 + j) 0 = ∑ j ∈ range L.length, eqQ.getD (acc.q + (j + 1)) 0 * corner *
          omega * ch.eps.getD (acc.q + (j + 1)) 0 :=
        sum_congr rfl fun j _ ↦ by rw [show acc.q + 1 + j = acc.q + (j + 1) by omega]
      rw [h2, hq, hcw, hs, List.length_cons, sum_range_succ']
      simp only [add_zero]
      ring
    · rw [h3, hp, hq, List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        List.append_assoc, List.singleton_append]
      simp only [add_zero, List.getD_cons_zero]
      congr 2
      refine List.map_congr_left fun j _ ↦ ?_
      simp only [Function.comp_apply, List.getD_cons_succ]
      congr 2
      omega

theorem zipIdx_getD_fst (l : List ℕ) {j : ℕ} (hj : j < l.length) : (l.zipIdx.getD j (0, 0)).1 = l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ hj, List.getElem_zipIdx]

theorem zipIdx_eq_map {α : Type} [Inhabited α] (l : List α) :
    l.zipIdx = (List.range l.length).map fun t ↦ (l.getD t default, t) := by
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  simp at h1
  simp [List.getElem_zipIdx, List.getElem?_eq_getElem h1]

theorem zipIdx_ptrsOf (t : ℕ) : ((layout.tables.map (·.links.pointers)).getD t []).zipIdx.length =
    (ptrsOf layout t).length := by simp [ptrsOf]

/-- The fold over the first `n` tables. -/
theorem rowFold_closed (message : List E) : ∀ n : ℕ,
    let rs := ((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)
    rs.q = qBase layout n ∧
    rs.certWeight = ∑ t ∈ range n, ∑ k ∈ range (ptrsOf layout t).length,
      eqQ.getD (qBase layout t + k) 0 * cornerAt layout chi t * omegaOf layout ch chi t *
        ch.eps.getD (qBase layout t + k) 0 ∧
    rs.pieces = (List.range n).flatMap fun t ↦
      (List.range (ptrsOf layout t).length).map (pieceAt layout chi eqQ t)
  | 0 => by simp [rowStart, qBase]
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := rowFold_closed message n
    rw [List.range_succ, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
      List.foldl_nil]
    set rs := ((List.range n).map fun t ↦ (layout.tables.getD t default, t)).foldl
      (rowStep layout ch a jump eqQ chi) (rowStart layout message)
    obtain ⟨p1, p2, p3⟩ := ptrFold_closed layout ch a eqQ _ _ _ _ _ _ (layout.tables.getD n default) n _
      ((layout.tables.map (·.links.pointers)).getD n []).zipIdx
      { rs with base := _, sent := _ }
    simp only [rowStep]
    refine ⟨?_, ?_, ?_⟩
    · rw [p1, zipIdx_ptrsOf]
      simp [h1, qBase_succ]
    · rw [p2, zipIdx_ptrsOf, sum_range_succ, h2]
      simp only [h1]
      rfl
    · rw [p3, zipIdx_ptrsOf, h3, List.flatMap_append, List.flatMap_singleton]
      congr 1
      refine List.map_congr_left fun k hk ↦ ?_
      have hk' := List.mem_range.mp hk
      rw [zipIdx_getD_fst _ (by simpa [ptrsOf] using hk')]
      simp [pieceAt, heightOf, h1, ptrsOf]

/-- **The row side in closed form** over all the tables. -/
theorem rowSideOf_closed (message : List E) :
    let rs := rowSideOf layout ch a jump eqQ chi message
    rs.q = qBase layout layout.tables.length ∧
    rs.certWeight = ∑ t ∈ range layout.tables.length, ∑ k ∈ range (ptrsOf layout t).length,
      eqQ.getD (qBase layout t + k) 0 * cornerAt layout chi t * omegaOf layout ch chi t *
        ch.eps.getD (qBase layout t + k) 0 ∧
    rs.pieces = (List.range layout.tables.length).flatMap fun t ↦
      (List.range (ptrsOf layout t).length).map (pieceAt layout chi eqQ t) := by
  have h := rowFold_closed layout ch a jump eqQ chi message layout.tables.length
  rw [← zipIdx_eq_map] at h
  exact h

end Fold

end

end LeanVM.Protocol.Relation
