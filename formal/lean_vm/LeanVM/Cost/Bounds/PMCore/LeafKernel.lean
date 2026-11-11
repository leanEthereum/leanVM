module

public import LeanVM.Cost.Bounds.PMCore.LeafReduce
import all CompPoly.LinearAlgebra.Dense.RowArray
public import CompPoly.LinearAlgebra.Dense.RowArrayCorrectness
public import CompPoly.LinearAlgebra.Dense.KernelBasisCorrectness
public import LeanVM.Cost.Bounds.PMLane.InterpDefs

/-!
# Bounds: the leaf's scalar kernel (row-array RREF), compiled

CompPoly's row-array RREF (`scalarRrefRows`, `Dense/RowArray.lean`) on `E` rows of at most `r`
entries: per column a pivot search (`43·E`), and per pivot a swap, a normalization (`r`
inverses) and an elimination of every other row (`69·r + E` each, a row written into the array).

* `findScalarPivotRowC_cost` (`43·(E − start) + 21`), `swapScalarRowsC_cost` (`2·E + 19`),
  `normalizeScalarRowC_cost` (`2871·r + 19`), `addScaledScalarRowC_cost` (`69·r + 29`);
* **`eliminateC_cost`** (`normalizeAndEliminateScalarRows`): at most
  `2871·r + (69·r + E + 87)·E + 66`, the rows keeping their count and widths.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.DenseMatrix

public section

/-- `E` rows of at most `r` entries. -/
@[expose] def RowsWithin (E r : ℕ) (rows : Array (Array K)) : Prop :=
  rows.size = E ∧ ∀ i, (rows.getD i #[]).size ≤ r

theorem rowsWithin_set {E r : ℕ} {rows : Array (Array K)} (h : RowsWithin E r rows) (i : ℕ)
    {v : Array K} (hv : v.size ≤ r) : RowsWithin E r (rows.setIfInBounds i v) := by
  refine ⟨by simp [h.1], fun j ↦ ?_⟩
  rw [array_getD_setIfInBounds]
  split_ifs
  · exact hv
  · exact h.2 j

theorem size_normalizeScalarRow (row : Array K) (c : ℕ) : (normalizeScalarRow row c).size = row.size := by
  unfold normalizeScalarRow; dsimp only; split_ifs <;> simp

theorem size_addScaledScalarRow (t s : Array K) (f : K) :
    (addScaledScalarRow t s f).size = max t.size s.size := by
  simp [addScaledScalarRow]

theorem rowsWithin_swap {E r : ℕ} {rows : Array (Array K)} (h : RowsWithin E r rows) (a b : ℕ) :
    RowsWithin E r (swapScalarRows rows a b) := by
  unfold swapScalarRows
  exact rowsWithin_set (rowsWithin_set h _ (h.2 b)) _ (h.2 a)

theorem foldl_inv {α β : Type*} (I : α → Prop) (f : α → β → α) (hf : ∀ a b, I a → I (f a b)) :
    ∀ (l : List β) (a : α), I a → I (l.foldl f a)
  | [], _, h => h
  | b :: l, a, h => foldl_inv I f hf l (f a b) (hf a b h)

/-- The elimination keeps the rows' count and widths. -/
theorem rowsWithin_normalizeAndEliminate {E r : ℕ} {rows : Array (Array K)} (h : RowsWithin E r rows)
    (p c : ℕ) : RowsWithin E r (normalizeAndEliminateScalarRows rows p c) := by
  unfold normalizeAndEliminateScalarRows
  dsimp only
  split_ifs
  · exact h
  · have hpv : (normalizeScalarRow (rows.getD p #[]) c).size ≤ r := by
      rw [size_normalizeScalarRow]; exact h.2 p
    refine foldl_inv (RowsWithin E r) _ (fun a b ha ↦ ?_) _ _ (rowsWithin_set h p hpv)
    split_ifs
    · exact ha
    · exact ha
    · exact rowsWithin_set ha b (by rw [size_addScaledScalarRow]; have := ha.2 b; omega)

variable (P : MachineProgram)

/-- The pivot search from `start`: at most `43·(E − start) + 21`. -/
theorem findScalarPivotRowC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.costDeps)
    (rows : Array (Array K)) (start col : ℕ) (hE : rows.size < 2 ^ 62) (hs : start ≤ rows.size) :
    machineCost P Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.costIdx
        [encodeValue rows, encodeValue start, encodeValue col] ≤ 43 * (rows.size - start) + 21 := by
  rw [Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.costEq P hP]
  have hr := rangeC_cost P (by includes) (rows.size - start) start (by omega)
  have hf := findNat_cost P (by includes) _
    (.closure Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.lam0.costIdx [encodeValue rows, encodeValue col])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.lam0.costSpec P
      (by includes) rows col a)) 14 (List.range' start (rows.size - start))
    (fun a _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.CompPoly.DenseMatrix.findScalarPivotRow.c499.lam0.costEq P (by includes)]
      simp)
  rw [limbs_of_lt (by omega : rows.size < 2 ^ 64), limbs_of_lt (by omega : start < 2 ^ 64)]
  simp only [List.length_range'] at hf
  omega

/-- The swap: `2·E + 19`. -/
theorem swapScalarRowsC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.swapScalarRows.c501.costDeps)
    (rows : Array (Array K)) (a b : ℕ) :
    machineCost P Auto.CompPoly.DenseMatrix.swapScalarRows.c501.costIdx
        [encodeValue rows, encodeValue a, encodeValue b] = 2 * rows.size + 19 := by
  rw [Auto.CompPoly.DenseMatrix.swapScalarRows.c501.costEq P hP]
  simp; omega

/-- The normalization of a row of at most `r` entries: at most `2871·r + 19`. -/
theorem normalizeScalarRowC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.costDeps)
    (row : Array K) (c r : ℕ) (hr : row.size ≤ r) :
    machineCost P Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.costIdx
        [encodeValue row, encodeValue c] ≤ 2871 * r + 19 := by
  rw [Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.costEq P hP]
  split_ifs
  · omega
  · have hm := map_cost P (by includes) (fun x ↦ x / row.getD c 0)
      (.closure Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.lam0.costIdx [encodeValue (row.getD c 0)])
      (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.lam0.costSpec P
        (by includes) (row.getD c 0) a)) 2854 row.toList (fun a _ ↦ by
        rw [appCost_fn, List.singleton_append, List.length_singleton,
          Auto.CompPoly.DenseMatrix.normalizeScalarRow.c503.lam0.costEq P (by includes)]
        have := invK_cost P (by includes) (row.getD c 0)
        omega)
    simp only [Array.length_toList, List.length_map] at hm ⊢
    omega

/-- `target + factor·source`, rows of at most `r` entries: at most `69·r + 29`. -/
theorem addScaledScalarRowC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.costDeps)
    (t s : Array K) (f : K) (r : ℕ) (hr : r < 2 ^ 62) (ht : t.size ≤ r) (hs : s.size ≤ r) :
    machineCost P Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.costIdx
        [encodeValue t, encodeValue s, encodeValue f] ≤ 69 * r + 29 := by
  rw [Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.costEq P hP]
  have hR := rangeLoop_cost P (by includes) (max t.size s.size) [] (by omega)
  have hm := map_cost P (by includes) (fun col ↦ t.getD col 0 + f * s.getD col 0)
    (.closure Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.lam0.costIdx
      [encodeValue t, encodeValue s, encodeValue f])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.lam0.costSpec P
      (by includes) t s f a)) 40 (List.range (max t.size s.size)) (fun a _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
        Auto.CompPoly.DenseMatrix.addScaledScalarRow.c506.lam0.costEq P (by includes)]
      simp)
  rw [limbs_of_lt (by omega : t.size < 2 ^ 64), limbs_of_lt (by omega : s.size < 2 ^ 64)]
  simp only [List.length_range, List.length_map, max_self] at hm ⊢
  have : max t.size s.size ≤ r := by omega
  split_ifs <;> omega

/-- **The normalization of the pivot row and the elimination of its column**
(`normalizeAndEliminateScalarRows`), `E` rows of at most `r` entries: at most
`2871·r + (69·r + E + 87)·E + 66`. -/
theorem eliminateC_cost
    (hP : Includes P Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.costDeps)
    {E r : ℕ} (hr : r < 2 ^ 62) (hE : E < 2 ^ 62) (rows : Array (Array K)) (h : RowsWithin E r rows)
    (p c : ℕ) (hp : p < 2 ^ 62) :
    machineCost P Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.costIdx
        [encodeValue rows, encodeValue p, encodeValue c] ≤ 2871 * r + (69 * r + E + 87) * E + 66 := by
  rw [Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.costEq P hP]
  split_ifs
  · omega
  · set pv := normalizeScalarRow (rows.getD p #[]) c with hpv
    have hpvs : pv.size ≤ r := by rw [hpv, size_normalizeScalarRow]; exact h.2 p
    have hn := normalizeScalarRowC_cost P (by includes) (rows.getD p #[]) c r (h.2 p)
    have h1 := rowsWithin_set h p hpvs
    have hR := rangeLoop_cost P (by includes) (rows.setIfInBounds p pv).size [] (by rw [h1.1]; omega)
    have hf := listFoldl_le P (by includes) _
      (.closure Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.lam0.costIdx
        [encodeValue p, encodeValue c, encodeValue pv])
      (fun a b ↦ RunsApp.of_spec
        (Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.lam0.costSpec P (by includes)
          p c pv a b)) (69 * r + E + 60) (RowsWithin E r) (List.range (rows.setIfInBounds p pv).size)
      (rows.setIfInBounds p pv) h1 (fun acc hacc b hb ↦ ⟨by
        dsimp only
        split_ifs
        · exact hacc
        · exact hacc
        · exact rowsWithin_set hacc b (by rw [size_addScaledScalarRow]; have := hacc.2 b; omega), by
        simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
        rw [Auto.CompPoly.DenseMatrix.normalizeAndEliminateScalarRows.c502.lam0.costEq P (by includes),
          limbs_of_lt (by have := List.mem_range.1 hb; rw [h1.1] at this; omega : b < 2 ^ 64),
          limbs_of_lt (by omega : p < 2 ^ 64)]
        have := addScaledScalarRowC_cost P (by includes) (acc.getD b #[]) pv
          (-(acc.getD b #[]).getD c 0) r hr (hacc.2 b) hpvs
        have := hacc.1
        split_ifs <;> simp only [max_self] <;> omega⟩)
    simp only [List.length_range] at hf
    have hsz := h1.1
    have e1 : (69 * r + E + 60 + 11) * (rows.setIfInBounds p pv).size = (69 * r + E + 60 + 11) * E := by
      rw [hsz]
    rw [h.1]
    have e : (69 * r + E + 60 + 11) * E + 16 * E = (69 * r + E + 87) * E := by ring
    omega

/-- **The RREF loop** (`scalarRrefRowsLoop`): `43·E + 56` per column, `pivotPrice E r` per pivot
(at most `E − row` of them). -/
theorem rrefLoopC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.scalarRrefRowsLoop.c498.costDeps)
    {E r : ℕ} (hr : r < 2 ^ 60) (hE : E < 2 ^ 60) (cols : ℕ) (hc : cols < 2 ^ 60) :
    ∀ (fuel col row : ℕ) (rows : Array (Array K)) (pivots : Array ℕ), RowsWithin E r rows →
      row ≤ E → pivots.size ≤ row → fuel + col < 2 ^ 60 →
      machineCost P Auto.CompPoly.DenseMatrix.scalarRrefRowsLoop.c498.costIdx
          [encodeValue cols, encodeValue fuel, encodeValue col, encodeValue row, encodeValue rows,
            encodeValue pivots] ≤ fuel * (43 * E + 56) + (E - row) * pivotPrice E r + 15 := by
  intro fuel
  induction fuel with
  | zero =>
    intro col row rows pivots _ _ _ _
    rw [Auto.CompPoly.DenseMatrix.scalarRrefRowsLoop.c498.costEq P hP]
    simp only [limbs_zero, Nat.rec_zero]
    omega
  | succ k ih =>
    intro col row rows pivots h hrow hpiv hfc
    rw [Auto.CompPoly.DenseMatrix.scalarRrefRowsLoop.c498.costEq P hP]
    have hE' := h.1
    rw [limbs_of_lt (by omega : k + 1 < 2 ^ 64), limbs_of_lt (by omega : cols < 2 ^ 64),
      limbs_of_lt (by omega : col < 2 ^ 64), limbs_of_lt (by omega : rows.size < 2 ^ 64),
      limbs_of_lt (by omega : row < 2 ^ 64)]
    have hc1 : limbCount (col + 1) = 1 := limbs_of_lt (by omega)
    have hr1 : limbCount (row + 1) = 1 := limbs_of_lt (by omega)
    simp only [max_self, hc1, hr1]
    have hmono : ∀ a b, a ≤ b → a * pivotPrice E r ≤ b * pivotPrice E r :=
      fun a b hab ↦ Nat.mul_le_mul_right _ hab
    have hk : (k + 1) * (43 * E + 56) = k * (43 * E + 56) + 43 * E + 56 := by ring
    have h0 := hmono 0 (E - row) (by omega)
    by_cases hdone : col ≥ cols ∨ row ≥ rows.size
    · have hd : (decide (col ≥ cols) || decide (row ≥ rows.size)) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]; exact hdone
      simp only [hd, ↓reduceIte]
      split_ifs <;> omega
    · have hd1 : decide (col ≥ cols) = false := by simp; omega
      have hd2 : decide (row ≥ rows.size) = false := by simp; omega
      simp only [hd1, hd2, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
      have hfind := findScalarPivotRowC_cost P (by includes) rows row col (by omega) (by omega)
      generalize hfv : findScalarPivotRow rows row col = fv
      cases fv with
      | none =>
        have := ih (col + 1) row rows pivots h hrow hpiv (by omega)
        simp only
        omega
      | some v =>
        have hrowlt : row < E := by omega
        have hsw := swapScalarRowsC_cost P (by includes) rows v row
        have hel := eliminateC_cost P (by includes) (E := E) (r := r) (by omega) (by omega)
          (swapScalarRows rows v row) (rowsWithin_swap h v row) row col (by omega)
        have := ih (col + 1) (row + 1) _ (pivots.push col)
          (rowsWithin_normalizeAndEliminate (rowsWithin_swap h v row) row col) (by omega)
          (by simp; omega) (by omega)
        have e : (E - row) * pivotPrice E r = (E - (row + 1)) * pivotPrice E r + pivotPrice E r := by
          rw [show E - row = E - (row + 1) + 1 by omega]; ring
        simp only
        have hpp : pivotPrice E r = 2871 * r + (69 * r + E + 87) * E + 3 * E + 100 := rfl
        omega

/-- **The RREF** (`scalarRrefRows`) of `E` rows of at most `r` entries over `cols` columns. -/
theorem scalarRrefRowsC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.scalarRrefRows.c497.costDeps)
    {E r : ℕ} (hr : r < 2 ^ 60) (hE : E < 2 ^ 60) (cols : ℕ) (hc : cols < 2 ^ 58)
    (rows : Array (Array K)) (h : RowsWithin E r rows) :
    machineCost P Auto.CompPoly.DenseMatrix.scalarRrefRows.c497.costIdx [encodeValue rows, encodeValue cols] ≤
      (cols + 1) * (43 * E + 56) + E * pivotPrice E r + 25 := by
  rw [Auto.CompPoly.DenseMatrix.scalarRrefRows.c497.costEq P hP, limbs_of_lt (by omega : cols < 2 ^ 64),
    limbs_of_lt (by omega : cols + 1 < 2 ^ 64)]
  have := rrefLoopC_cost P (by includes) hr hE cols (by omega) (cols + 1) 0 0 rows #[] h (by omega)
    (by simp) (by omega)
  simp only [Nat.sub_zero] at this
  omega

/-- `containsNat xs x`: at most `18·|xs| + 9`. -/
theorem containsNatC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.containsNat.c514.costDeps)
    (xs : Array ℕ) (x : ℕ) (hx : x < 2 ^ 64) (hxs : ∀ y ∈ xs, y < 2 ^ 64) :
    machineCost P Auto.CompPoly.DenseMatrix.containsNat.c514.costIdx [encodeValue xs, encodeValue x] ≤
      18 * xs.size + 9 := by
  rw [Auto.CompPoly.DenseMatrix.containsNat.c514.costEq P hP]
  have hf := fun a ↦ RunsApp.of_spec (us := [encodeValue x]) (vs := [encodeValue a])
    (placementsOfC.lam2.lam0.costSpec P (by includes) x a)
  have key : ∀ l : List ℕ, (∀ y ∈ l, y < 2 ^ 64) →
      machineCost P Auto.List.any.c15.costIdx
          [encodeValue l, .closure placementsOfC.lam2.lam0.costIdx [encodeValue x]] ≤ 15 * l.length + 3 := by
    intro l
    induction l with
    | nil =>
      intro _
      rw [Auto.List.any.c15.costEq_nil P (by includes) _
        (.closure placementsOfC.lam2.lam0.costIdx [encodeValue x]) hf]
      omega
    | cons a l ih =>
      intro hl
      rw [Auto.List.any.c15.costEq_cons P (by includes) a l _
        (.closure placementsOfC.lam2.lam0.costIdx [encodeValue x]) hf]
      have h1 := ih fun y hy ↦ hl y (by simp [hy])
      rw [appCost_fn, List.singleton_append, placementsOfC.lam2.lam0.costEq P (by includes),
        limbs_of_lt (hl a (by simp)), limbs_of_lt hx]
      simp only [List.length_cons, List.length_nil, max_self]
      split_ifs <;> omega
  have := key xs.toList (fun y hy ↦ hxs y (by simpa using hy))
  simp only [Array.length_toList] at this
  omega

/-- `pivotRowOfColumn? pivots col`: at most `34·|pivots| + 18`. -/
theorem pivotRowOfColumnC_cost (hP : Includes P Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.costDeps)
    (pivots : Array ℕ) (col : ℕ) (hc : col < 2 ^ 64) (hp : ∀ i, pivots.getD i 0 < 2 ^ 64)
    (hs : pivots.size < 2 ^ 62) :
    machineCost P Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.costIdx [encodeValue pivots, encodeValue col] ≤
      34 * pivots.size + 18 := by
  rw [Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.costEq P hP]
  have hr := rangeLoop_cost P (by includes) pivots.size [] (by omega)
  have hf := findNat_cost P (by includes) _
    (.closure Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.lam0.costIdx [encodeValue pivots, encodeValue col])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.lam0.costSpec P
      (by includes) pivots col a)) 8 (List.range pivots.size) (fun a _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        Auto.CompPoly.DenseMatrix.pivotRowOfColumn?.c511.lam0.costEq P (by includes),
        limbs_of_lt (hp a), limbs_of_lt hc]
      simp)
  simp only [List.length_range] at hf
  omega

/-- The pivots of the RREF: column indices below `cols`, at most `cols` of them. -/
theorem rref_pivots (rows : Array (Array K)) (cols : ℕ) :
    (∀ i, (scalarRrefRows rows cols).pivots.getD i 0 < cols ∨ (scalarRrefRows rows cols).pivots.getD i 0 = 0) ∧
      (scalarRrefRows rows cols).pivots.size ≤ cols ∧
      (freeColumns cols (scalarRrefRows rows cols).pivots).size ≤ cols := by
  have hs := scalarRrefRows_spec rows cols
  have h := freeColumns_size_add_pivots_size (cols := cols)
    (pivots := (scalarRrefRows rows cols).pivots)
    (fun i j hi hj hij ↦ hs.mono i j hij hj) hs.pivots_lt
  refine ⟨fun i ↦ ?_, by omega, by omega⟩
  rcases Nat.lt_or_ge i (scalarRrefRows rows cols).pivots.size with hi | hi
  · exact Or.inl (hs.pivots_lt i hi)
  · right; rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi]; rfl

/-- One kernel vector (`basisVectorForFreeColumnRows`): at most `(34·p + 56)·cols + 18`, `p` the
pivots. -/
theorem basisVectorC_cost
    (hP : Includes P Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.costDeps)
    (rows : Array (Array K)) (pivots : Array ℕ) (cols free : ℕ) (hc : cols < 2 ^ 60)
    (hf : free < 2 ^ 64) (hp : ∀ i, pivots.getD i 0 < 2 ^ 64) (hps : pivots.size < 2 ^ 60) :
    machineCost P Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.costIdx
        [encodeValue rows, encodeValue pivots, encodeValue cols, encodeValue free] ≤
      (34 * pivots.size + 56) * cols + 18 := by
  rw [Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.costEq P hP]
  have hof := ofFnFrom_cost P (by includes) (by omega : cols < 2 ^ 64) _
    (.closure Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.lam0.costIdx
      [encodeValue rows, encodeValue pivots, encodeValue cols, encodeValue free])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.lam0.costSpec P
      (by includes) rows pivots cols free a)) (34 * pivots.size + 39) (fun a ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.DenseMatrix.basisVectorForFreeColumnRows.c509.lam0.costEq P (by includes),
        limbs_of_lt (by have := a.isLt; omega : (a : ℕ) < 2 ^ 64), limbs_of_lt hf]
      have := pivotRowOfColumnC_cost P (by includes) pivots a (by have := a.isLt; omega) hp (by omega)
      simp only [max_self]
      split_ifs
      · omega
      · cases pivotRowOfColumn? pivots a <;> dsimp only <;> omega) 0 (Nat.zero_le _)
  rw [ofFnFrom_length]
  simp only [Nat.sub_zero] at hof
  nlinarith

/-- **The scalar kernel basis** (`homogeneousKernelBasisRows`) of `E` rows of at most `r` entries
over `cols` columns. -/
theorem kernelBasisC_cost
    (hP : Includes P Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.costDeps)
    {E r : ℕ} (hr : r < 2 ^ 58) (hE : E < 2 ^ 58) (cols : ℕ) (hc : cols < 2 ^ 30)
    (rows : Array (Array K)) (h : RowsWithin E r rows) :
    machineCost P Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.costIdx
        [encodeValue rows, encodeValue cols] ≤
      (cols + 1) * (43 * E + 56) + E * pivotPrice E r + (34 * cols + 56) * cols * cols +
        (18 * cols + 91) * cols + 62 := by
  rw [Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.costEq P hP]
  obtain ⟨hpl, hps, hfs⟩ := rref_pivots rows cols
  set R := scalarRrefRows rows cols with hR
  have hpw : ∀ i, R.pivots.getD i 0 < 2 ^ 64 := fun i ↦ by rcases hpl i with h | h <;> omega
  have hrref := scalarRrefRowsC_cost P (by includes) (E := E) (r := r) (by omega) (by omega) cols
    (by omega) rows h
  have hrl := rangeLoop_cost P (by includes) cols [] (by omega)
  have hfilt := filter_cost P (by includes) (fun col ↦ !containsNat R.pivots col)
    (.closure Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam1.costIdx [encodeValue R])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam1.costSpec P
      (by includes) R a)) (18 * cols + 16) (List.range cols) (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, List.length_singleton,
        Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam1.costEq P (by includes)]
      have := containsNatC_cost P (by includes) R.pivots a (by have := List.mem_range.1 ha; omega)
        (fun y hy ↦ by
          obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hy
          have := hpw i
          rwa [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at this)
      omega)
  have hm := map_cost P (by includes) (basisVectorForFreeColumnRows R.rows R.pivots cols)
    (.closure Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam0.costIdx
      [encodeValue cols, encodeValue R.pivots, encodeValue R.rows, encodeValue R])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam0.costSpec P
      (by includes) cols R.pivots R.rows R a)) ((34 * cols + 56) * cols + 27)
    (freeColumns cols R.pivots).toList (fun a ha ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.DenseMatrix.homogeneousKernelBasisRows.c496.lam0.costEq P (by includes)]
      have ha' : a < cols := by
        simp only [freeColumns, List.toList_toArray, List.mem_filter, List.mem_range] at ha
        exact ha.1
      have := basisVectorC_cost P (by includes) R.rows R.pivots cols a (by omega) (by omega) hpw
        (by omega)
      have : (34 * R.pivots.size + 56) * cols ≤ (34 * cols + 56) * cols :=
        Nat.mul_le_mul_right _ (by omega)
      omega)
  have hfl := List.length_filter_le (fun col ↦ !containsNat R.pivots col) (List.range cols)
  simp only [List.length_range, Array.length_toList, List.length_map] at hfilt hm hfl ⊢
  have e1 : ((34 * cols + 56) * cols + 27 + 13) * (freeColumns cols R.pivots).size ≤
      ((34 * cols + 56) * cols + 40) * cols := Nat.mul_le_mul_left _ hfs
  have e3 : ((34 * cols + 56) * cols + 40) * cols = (34 * cols + 56) * cols * cols + 40 * cols := by
    ring
  have e4 : (18 * cols + 16 + 15) * cols + 60 * cols = (18 * cols + 91) * cols := by ring
  omega

end

end LeanVM.Cost.Bounds.PMCore
