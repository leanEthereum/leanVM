module

public import LeanVM.Cost.Bounds.PMCore.LeafPivot
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic

public import LeanVM.Cost.Bounds.PMLane.InterpDefs
/-!
# Bounds: the leaf's incremental reduction, compiled

`reduceKernelLeafRowsIncremental` (CompPoly, `KernelLeaf.lean`) inserts the scalar kernel rows and
the completion rows one at a time: each insertion rebuilds the pivot table from the current basis
and the new row (`reduceKernelLeafRowsByPivots`), reads its rows back (`pivotRows`) and drops the
zero ones. On rows `X^e·v`, `e ≤ 1`, of width `r` (`BasisInv`), the rank potential telescopes
over all insertions (`insertPivotC_cost`): **`reduceIncrementalC_cost`**, for `n` rows,
`n·incPrice r + stepPrice r·2r·n`.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Extraction.Fast.PMDegree (HomRowLe homRowLe_cancel)

public section

/-- Rows `X^e·v`, `e ≤ 1`, of width `r`. -/
@[expose] def RowsInv (r : ℕ) (rows : List (PolynomialRow K)) : Prop :=
  ∀ q ∈ rows, q.size = r ∧ HomRowLe 1 q

/-- The potential of a list of rows: their ranks. -/
@[expose] def psi (r : ℕ) (shift : Array ℕ) (rows : List (PolynomialRow K)) : ℕ :=
  (rows.map (rk r shift)).sum

theorem psi_filterMap (r : ℕ) (shift : Array ℕ) :
    ∀ l : List (Option (PolynomialRow K)), psi r shift (l.filterMap id) = (l.map (rkOpt r shift)).sum
  | [] => rfl
  | none :: l => by simp [psi, rkOpt] at *; exact psi_filterMap r shift l
  | some q :: l => by
    have := psi_filterMap r shift l
    simp only [psi, List.filterMap_cons, id, List.map_cons, List.sum_cons, rkOpt, Option.elim_some]
      at this ⊢
    omega

theorem psi_filter_le (r : ℕ) (shift : Array ℕ) (f : PolynomialRow K → Bool) :
    ∀ l : List (PolynomialRow K), psi r shift (l.filter f) ≤ psi r shift l
  | [] => le_rfl
  | q :: l => by
    have := psi_filter_le r shift f l
    simp only [psi, List.filter_cons] at this ⊢
    split <;> simp only [List.map_cons, List.sum_cons] <;> omega

theorem psi_le (r : ℕ) (shift : Array ℕ) (l : List (PolynomialRow K)) :
    psi r shift l ≤ 2 * r * l.length := by
  induction l with
  | nil => simp [psi]
  | cons q l ih =>
    have := rk_le r shift q
    simp only [psi, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [Nat.mul_succ]
    omega

/-- The table's rows read back: the rows of a `TableInv` table. -/
theorem rowsInv_pivotRows {r : ℕ} {shift : Array ℕ} {T : Array (Option (PolynomialRow K))}
    (hT : TableInv r shift T) : RowsInv r (pivotRows T).toList := by
  intro q hq
  simp only [pivotRows, List.toList_toArray, List.mem_filterMap, id] at hq
  obtain ⟨o, ho, rfl⟩ := hq
  obtain ⟨p, hp, hpo⟩ := List.getElem_of_mem ho
  have hp' : p < T.size := by simpa using hp
  have := hT.2 p q (by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp', ← Array.getElem_toList hp']
    simp [hpo])
  exact ⟨this.1, this.2.1⟩

theorem pivotRows_size_le (T : Array (Option (PolynomialRow K))) : (pivotRows T).size ≤ T.size := by
  simp only [pivotRows, List.size_toArray]
  exact (List.length_filterMap_le _ _).trans (by simp)

variable (P : MachineProgram)

/-- **The table built from a list of rows** (the fold of `reduceKernelLeafRowsByPivots`):
`18 + c` per row (`c = stepPrice r`), the potential. -/
theorem foldInsertC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 40) (hS40 : S < 2 ^ 60) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (fuel : ℕ) (hfuel : fuel < 2 ^ 128) :
    ∀ (l : List (PolynomialRow K)) (T : Array (Option (PolynomialRow K))), TableInv r shift T →
      RowsInv r l →
      machineCost P listFoldl.costIdx
          [.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.lam0.costIdx
            [encodeValue shift, encodeValue fuel], encodeValue T, encodeValue l] +
          stepPrice r * phi r shift
            (l.foldl (fun pivots row ↦ insertKernelLeafPivotRowWithFuel fuel pivots shift row) T) ≤
        stepPrice r * (phi r shift T + psi r shift l) + (stepPrice r + 18) * l.length + 3 ∧
      TableInv r shift
        (l.foldl (fun pivots row ↦ insertKernelLeafPivotRowWithFuel fuel pivots shift row) T) := by
  have hf := fun a b ↦ RunsApp.of_spec (us := [encodeValue shift, encodeValue fuel])
    (vs := [encodeValue a, encodeValue b])
    (Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.lam0.costSpec P
      (by includes) shift fuel a b)
  intro l
  induction l with
  | nil =>
    intro T hT _
    rw [listFoldl.costEq_nil P (by includes)
      (fun pivots row ↦ insertKernelLeafPivotRowWithFuel fuel pivots shift row)
      (.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.lam0.costIdx
        [encodeValue shift, encodeValue fuel]) hf]
    simp [psi]
    exact ⟨by omega, hT⟩
  | cons q l ih =>
    intro T hT hl
    rw [listFoldl.costEq_cons P (by includes)
      (fun pivots row ↦ insertKernelLeafPivotRowWithFuel fuel pivots shift row)
      (.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.lam0.costIdx
        [encodeValue shift, encodeValue fuel]) hf]
    obtain ⟨hqs, hqh⟩ := hl q (by simp)
    obtain ⟨h1, hT'⟩ := insertPivotC_cost P (by includes) hr hS40 shift hS fuel T q hfuel hT hqs hqh
    obtain ⟨h2, hT''⟩ := ih _ hT' (fun x hx ↦ hl x (by simp [hx]))
    refine ⟨?_, hT''⟩
    simp only [appCost_fn, List.cons_append, List.nil_append, List.foldl_cons, List.length_cons,
      List.length_nil, psi, List.map_cons, List.sum_cons] at h2 ⊢
    rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.lam0.costEq P
      (by includes)]
    have e1 : stepPrice r * (phi r shift T + (rk r shift q + (List.map (rk r shift) l).sum)) =
        stepPrice r * (phi r shift T + rk r shift q) + stepPrice r * (List.map (rk r shift) l).sum := by
      ring
    have e2 : stepPrice r * (phi r shift (insertKernelLeafPivotRowWithFuel fuel T shift q) +
        (List.map (rk r shift) l).sum) = stepPrice r * phi r shift
          (insertKernelLeafPivotRowWithFuel fuel T shift q) +
        stepPrice r * (List.map (rk r shift) l).sum := by ring
    have e3 : (stepPrice r + 18) * (l.length + 1) = (stepPrice r + 18) * l.length + stepPrice r + 18 := by
      ring
    omega

theorem rowWithin_of_rowsInv {r : ℕ} {rows : PolynomialMatrix K} (h : RowsInv r rows.toList) (i : ℕ) :
    RowWithin r 2 (rows.getD i #[]) := by
  rcases Nat.lt_or_ge i rows.size with hi | hi
  · have hmem : rows.getD i #[] ∈ rows.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]; simp
    obtain ⟨hs, hh⟩ := h _ hmem
    exact rowWithin_of_homRow hs hh
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    exact RowWithin.empty _ _

/-- The fold of the fuel: every row's shifted degree at most `2 + S`. -/
theorem fuelFold_le {r S : ℕ} {rows : PolynomialMatrix K} (h : RowsInv r rows.toList)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 2 + S →
      l.foldl (fun acc i ↦ Option.casesOn (rowShiftedDegree? (rows.getD i #[]) shift) acc
        fun val ↦ max acc val) acc ≤ 2 + S := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    cases hv : rowShiftedDegree? (rows.getD i #[]) shift with
    | none => exact hacc
    | some v =>
      have := rowShiftedDegree?_le (rowWithin_of_rowsInv h i) hS hv
      simp only
      omega

theorem fuelFold_le' {r S : ℕ} {rows : PolynomialMatrix K} (h : RowsInv r rows.toList)
    {shift : Array ℕ} (hS : ∀ j, shift.getD j 0 ≤ S) :
    ∀ (l : List ℕ) (acc : ℕ), acc ≤ 2 + S →
      l.foldl (fun acc i ↦ match rowShiftedDegree? (rows.getD i #[]) shift with
        | none => acc
        | some degree => max acc degree) acc ≤ 2 + S := by
  intro l
  induction l with
  | nil => intro acc h; exact h
  | cons i l ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    apply ih
    cases hv : rowShiftedDegree? (rows.getD i #[]) shift with
    | none => exact hacc
    | some v =>
      have := rowShiftedDegree?_le (rowWithin_of_rowsInv h i) hS hv
      simp only
      omega

theorem reduceKernelLeafFuel_lt {r S : ℕ} (hr : r < 2 ^ 30) (hS : S < 2 ^ 60) {rows : PolynomialMatrix K}
    (h : RowsInv r rows.toList) (hn : rows.size ≤ r + 1) {shift : Array ℕ}
    (hSs : ∀ j, shift.getD j 0 ≤ S) (hw : MatrixWidth rows ≤ r) :
    reduceKernelLeafFuel rows shift < 2 ^ 128 := by
  unfold reduceKernelLeafFuel
  have := fuelFold_le' h hSs (List.range rows.size) 0 (by omega)
  dsimp only
  generalize List.foldl _ 0 (List.range rows.size) = M at this ⊢
  have h1 : (rows.size + 1) * (MatrixWidth rows + 1) ≤ 2 ^ 31 * 2 ^ 31 :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2 := Nat.mul_le_mul h1 (show M + 1 ≤ 2 ^ 61 by omega)
  have : (2 : ℕ) ^ 31 * 2 ^ 31 * 2 ^ 61 < 2 ^ 128 := by norm_num
  omega

variable (P : MachineProgram)

/-- **The fuel** (`reduceKernelLeafFuel`): `n ≤ r + 1` rows: at most `(84·r + 63)·n + 49`. -/
theorem reduceKernelLeafFuelC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 30) (hS40 : S < 2 ^ 60) (rows : PolynomialMatrix K)
    (h : RowsInv r rows.toList) (hn : rows.size ≤ r + 1) (shift : Array ℕ)
    (hS : ∀ j, shift.getD j 0 ≤ S) (hw : MatrixWidth rows ≤ r) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.costIdx
        [encodeValue rows, encodeValue shift] ≤ (84 * r + 63) * rows.size + 49 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.costEq P hP]
  have hr' := rangeLoop_cost P (by includes) rows.size [] (by omega)
  have hmw := matrixWidthC_cost P (by includes) rows (by omega)
  have hf := listFoldl_le P (by includes) _
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.lam0.costIdx
      [encodeValue rows, encodeValue shift])
    (fun a b ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.lam0.costSpec P
        (by includes) rows shift a b))
    (84 * r + 37) (fun acc ↦ acc ≤ 2 + S) (List.range rows.size) 0 (by omega)
    (fun acc hacc i _ ↦ ⟨by
      cases hv : rowShiftedDegree? (rows.getD i #[]) shift with
      | none => exact hacc
      | some v =>
        have := rowShiftedDegree?_le (rowWithin_of_rowsInv h i) hS hv
        simp only; omega, by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafFuel.c531.lam0.costEq P
        (by includes)]
      have := rowShiftedDegree_cost P (by includes) (C := r) (D := 2) (S := S) (by omega) (by omega)
        (rows.getD i #[]) (rowWithin_of_rowsInv h i) shift hS
      cases hv : rowShiftedDegree? (rows.getD i #[]) shift with
      | none => dsimp only; omega
      | some v =>
        have := rowShiftedDegree?_le (rowWithin_of_rowsInv h i) hS hv
        dsimp only
        rw [limbs_of_lt (by omega : acc < 2 ^ 64), limbs_of_lt (by omega : v < 2 ^ 64)]
        split_ifs <;> simp only [max_self] <;> omega⟩)
  have hmax := fuelFold_le h hS (List.range rows.size) 0 (by omega)
  set M := (List.range rows.size).foldl (fun acc i ↦ Option.casesOn
    (rowShiftedDegree? (rows.getD i #[]) shift) acc fun val ↦ max acc val) 0 with hM
  simp only [List.length_range] at hf
  rw [limbs_of_lt (by omega : rows.size < 2 ^ 64), limbs_of_lt (by omega : MatrixWidth rows < 2 ^ 64),
    limbs_of_lt (by omega : rows.size + 1 < 2 ^ 64),
    limbs_of_lt (by omega : MatrixWidth rows + 1 < 2 ^ 64),
    limbs_of_lt (by omega : M < 2 ^ 64), limbs_of_lt (by omega : M + 1 < 2 ^ 64),
    limbs_of_lt (show (rows.size + 1) * (MatrixWidth rows + 1) < 2 ^ 64 by
      have := Nat.mul_le_mul (show rows.size + 1 ≤ 2 ^ 31 by omega)
        (show MatrixWidth rows + 1 ≤ 2 ^ 31 by omega)
      omega)]
  have h3 := limbs_le_two (show (rows.size + 1) * (MatrixWidth rows + 1) * (M + 1) < 2 ^ 128 by
    have := Nat.mul_le_mul (show rows.size + 1 ≤ 2 ^ 31 by omega)
      (show MatrixWidth rows + 1 ≤ 2 ^ 31 by omega)
    have := Nat.mul_le_mul this (show M + 1 ≤ 2 ^ 61 by omega)
    omega)
  have h4 : max (limbCount ((rows.size + 1) * (MatrixWidth rows + 1) * (M + 1))) (1 * 1) ≤ 2 := by
    omega
  simp only [max_self] at h4 ⊢
  nlinarith

/-- **`pivotRows`**: at most `21·|T| + 8`. -/
theorem pivotRowsC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.costDeps)
    (T : Array (Option (PolynomialRow K))) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.costIdx [encodeValue T] ≤
      21 * T.size + 8 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.costEq P hP]
  have hf := filterMap_cost P (by includes) (id : Option (PolynomialRow K) → Option (PolynomialRow K))
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.lam0.costSpec P (by includes) a))
    1 T.toList (fun a _ ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil,
        Auto.CompPoly.PolynomialMatrix.Approximant.pivotRows.c545.lam0.costEq P (by includes)])
  have := List.length_filterMap_le id T.toList
  simp only [Array.length_toList] at hf this
  omega

theorem phi_replicate (r : ℕ) (shift : Array ℕ) (n : ℕ) :
    phi r shift (Array.replicate n none) = 0 := by
  unfold phi
  simp [rkOpt]

theorem tableInv_replicate (r : ℕ) (shift : Array ℕ) :
    TableInv r shift (Array.replicate r (none : Option (PolynomialRow K))) := by
  refine ⟨by simp, fun p q hq ↦ ?_⟩
  rw [Array.getD_eq_getD_getElem?] at hq
  rcases Nat.lt_or_ge p r with hp | hp
  · rw [Array.getElem?_eq_getElem (by simpa using hp), Array.getElem_replicate] at hq; cases hq
  · rw [Array.getElem?_eq_none (by simpa using hp)] at hq; cases hq

theorem matrixWidth_of_rowsInv {r : ℕ} {rows : PolynomialMatrix K} (h : RowsInv r rows.toList)
    (hn : 1 ≤ rows.size) : MatrixWidth rows = r := by
  unfold MatrixWidth
  rw [Array.getElem?_eq_getElem (by omega)]
  exact (h _ (Array.getElem_mem_toList _)).1

theorem phi_eq_psi_pivotRows (r : ℕ) (shift : Array ℕ) (T : Array (Option (PolynomialRow K))) :
    psi r shift (pivotRows T).toList = phi r shift T := by
  simp only [pivotRows, List.toList_toArray, phi]
  exact psi_filterMap r shift T.toList

/-- **The table rebuilt** (`reduceKernelLeafRowsByPivots`), `n ≤ r + 1` rows, the potential. -/
theorem byPivotsC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 30) (hS40 : S < 2 ^ 60) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (rows : PolynomialMatrix K) (h : RowsInv r rows.toList) (hn1 : 1 ≤ rows.size)
    (hn : rows.size ≤ r + 1) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.costIdx
        [encodeValue rows, encodeValue shift] +
        stepPrice r * psi r shift (reduceKernelLeafRowsByPivots rows shift).toList ≤
      stepPrice r * psi r shift rows.toList + (stepPrice r + 18) * rows.size +
        (84 * r + 66) * rows.size + 22 * r + 94 ∧
      RowsInv r (reduceKernelLeafRowsByPivots rows shift).toList ∧
      (reduceKernelLeafRowsByPivots rows shift).size ≤ r := by
  have hw := matrixWidth_of_rowsInv h hn1
  have hfuel := reduceKernelLeafFuel_lt hr hS40 h hn hS (by omega)
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsByPivots.c530.costEq P hP]
  have hfc := reduceKernelLeafFuelC_cost P (by includes) hr hS40 rows h hn shift hS (by omega)
  have hmw := matrixWidthC_cost P (by includes) rows (by omega)
  obtain ⟨hfold, hT⟩ := foldInsertC_cost P (by includes) (r := r) (S := S) (by omega) hS40 shift hS
    (reduceKernelLeafFuel rows shift) hfuel rows.toList (Array.replicate (MatrixWidth rows) none)
    (by rw [hw]; exact tableInv_replicate r shift) h
  rw [phi_replicate, Nat.zero_add] at hfold
  set T := rows.toList.foldl (fun pivots row ↦ insertKernelLeafPivotRowWithFuel
    (reduceKernelLeafFuel rows shift) pivots shift row) (Array.replicate (MatrixWidth rows) none) with hTdef
  have hTa : Array.foldl (fun pivots row ↦ insertKernelLeafPivotRowWithFuel
      (reduceKernelLeafFuel rows shift) pivots shift row) (Array.replicate (MatrixWidth rows) none) rows = T := by
    rw [hTdef, Array.foldl_toList]
  have hres : reduceKernelLeafRowsByPivots rows shift = pivotRows T := by
    rw [reduceKernelLeafRowsByPivots, ← hTa]
  rw [hTa, hres, phi_eq_psi_pivotRows]
  have hpr := pivotRowsC_cost P (by includes) T
  rw [hT.1] at hpr
  simp only [Array.length_toList] at hfold
  have e : (84 * r + 63) * rows.size + 3 * rows.size = (84 * r + 66) * rows.size := by ring
  refine ⟨by omega, rowsInv_pivotRows hT, (pivotRows_size_le T).trans hT.1.le⟩

/-- **One incremental insertion** (`insertKernelLeafRowIncremental`): a basis of at most `r` rows
and a new row, the potential. -/
theorem insertIncrementalC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafRowIncremental.c528.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 30) (hS40 : S < 2 ^ 60) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (basis : PolynomialMatrix K) (hb : RowsInv r basis.toList) (hbs : basis.size ≤ r)
    (row : PolynomialRow K) (hrs : row.size = r) (hrh : HomRowLe 1 row) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafRowIncremental.c528.costIdx
        [encodeValue basis, encodeValue shift, encodeValue row] +
        stepPrice r * psi r shift (insertKernelLeafRowIncremental basis shift row).toList ≤
      stepPrice r * (psi r shift basis.toList + rk r shift row) + incPrice r ∧
      RowsInv r (insertKernelLeafRowIncremental basis shift row).toList ∧
      (insertKernelLeafRowIncremental basis shift row).size ≤ r := by
  have hpush : RowsInv r (basis.push row).toList := by
    intro q hq
    rw [Array.toList_push, List.mem_append] at hq
    rcases hq with hq | hq
    · exact hb q hq
    · rw [List.mem_singleton] at hq; subst hq; exact ⟨hrs, hrh⟩
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.insertKernelLeafRowIncremental.c528.costEq P hP,
    Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRows.c529.costEq P (by includes)]
  obtain ⟨hbp, hinv, hsz⟩ := byPivotsC_cost P (by includes) hr hS40 shift hS (basis.push row) hpush
    (by simp) (by simp; omega)
  have hred : reduceKernelLeafRows (basis.push row) shift =
      reduceKernelLeafRowsByPivots (basis.push row) shift := rfl
  rw [hred]
  set res := reduceKernelLeafRowsByPivots (basis.push row) shift with hresd
  have hfilt := filter_cost P (by includes) (fun row ↦ !rowIsZero row)
    (.closure compactNonzeroRowsC.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (compactNonzeroRowsC.lam0.costSpec P (by includes) a))
    ((3 * 2 + 33) * r + 11) res.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, compactNonzeroRowsC.lam0.costEq P (by includes)]
      obtain ⟨has, hah⟩ := hinv a ha
      have := rowIsZeroC_cost P (by includes) a (rowWithin_of_homRow has hah)
      omega)
  have hl := List.length_filter_le (fun row ↦ !rowIsZero row) res.toList
  have hres' : insertKernelLeafRowIncremental basis shift row = res.filter fun row ↦ !rowIsZero row := rfl
  have hpsi := psi_filter_le r shift (fun row ↦ !rowIsZero row) res.toList
  rw [hres']
  simp only [Array.length_toList, Array.toList_filter] at hfilt hl hpsi ⊢
  have hpp : psi r shift (basis.push row).toList = psi r shift basis.toList + rk r shift row := by
    simp [psi, Array.toList_push]
  rw [hpp] at hbp
  have hsp : (basis.push row).size = basis.size + 1 := by simp
  rw [hsp] at hbp
  have e1 : (stepPrice r + 18) * (basis.size + 1) ≤ (r + 1) * (stepPrice r + 18) := by
    rw [Nat.mul_comm (r + 1)]; exact Nat.mul_le_mul_left _ (by omega)
  have e2 : (84 * r + 66) * (basis.size + 1) ≤ (84 * r + 66) * (r + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have e3 : ((3 * 2 + 33) * r + 11 + 15) * res.size + res.size + 3 * res.size ≤ (39 * r + 30) * r := by
    have : ((3 * 2 + 33) * r + 11 + 15) * res.size + res.size + 3 * res.size =
      (39 * r + 30) * res.size := by ring
    rw [this]; exact Nat.mul_le_mul_left _ hsz
  have e4 : stepPrice r * psi r shift (List.filter (fun row ↦ !rowIsZero row) res.toList) ≤
      stepPrice r * psi r shift res.toList := Nat.mul_le_mul_left _ hpsi
  refine ⟨?_, fun q hq ↦ hinv q (List.mem_filter.1 hq).1, by
    have := List.length_filter_le (fun row ↦ !rowIsZero row) res.toList
    simp only [Array.length_toList] at this
    exact Array.size_filter_le.trans hsz⟩
  unfold incPrice
  omega

/-- **The incremental reduction** (`reduceKernelLeafRowsIncremental`) of `n` rows `X^e·v` of
width `r`: at most `stepPrice r·2r·n + (incPrice r + 19)·n + 11`; its rows are at most `r` such
rows. -/
theorem reduceIncrementalC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.costDeps)
    {r S : ℕ} (hr : r < 2 ^ 30) (hS40 : S < 2 ^ 60) (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S)
    (rows : PolynomialMatrix K) (h : RowsInv r rows.toList) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.costIdx
        [encodeValue rows, encodeValue shift] ≤
      stepPrice r * (2 * r * rows.size) + (incPrice r + 19) * rows.size + 11 ∧
      RowsInv r (reduceKernelLeafRowsIncremental rows shift).toList ∧
      (reduceKernelLeafRowsIncremental rows shift).size ≤ r := by
  have hf := fun a b ↦ RunsApp.of_spec (us := [encodeValue shift]) (vs := [encodeValue a, encodeValue b])
    (Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.lam0.costSpec P
      (by includes) shift a b)
  have key : ∀ (l : List (PolynomialRow K)) (basis : PolynomialMatrix K), RowsInv r basis.toList →
      basis.size ≤ r → RowsInv r l →
      machineCost P listFoldl.costIdx
          [.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.lam0.costIdx
            [encodeValue shift], encodeValue basis, encodeValue l] +
          stepPrice r * psi r shift
            (l.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis).toList ≤
        stepPrice r * (psi r shift basis.toList + psi r shift l) + (incPrice r + 16) * l.length + 3 ∧
      RowsInv r (l.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis).toList ∧
      (l.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) basis).size ≤ r := by
    intro l
    induction l with
    | nil =>
      intro basis hb hbs _
      rw [listFoldl.costEq_nil P (by includes)
        (fun basis row ↦ insertKernelLeafRowIncremental basis shift row)
        (.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.lam0.costIdx
          [encodeValue shift]) hf]
      simp only [List.foldl_nil, psi, List.map_nil, List.sum_nil, Nat.add_zero, List.length_nil,
        Nat.mul_zero]
      exact ⟨by omega, hb, hbs⟩
    | cons q l ih =>
      intro basis hb hbs hl
      rw [listFoldl.costEq_cons P (by includes)
        (fun basis row ↦ insertKernelLeafRowIncremental basis shift row)
        (.closure Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.lam0.costIdx
          [encodeValue shift]) hf]
      obtain ⟨hqs, hqh⟩ := hl q (by simp)
      obtain ⟨h1, hb', hbs'⟩ := insertIncrementalC_cost P (by includes) hr hS40 shift hS basis hb hbs
        q hqs hqh
      obtain ⟨h2, hfin, hfs⟩ := ih _ hb' hbs' (fun x hx ↦ hl x (by simp [hx]))
      refine ⟨?_, hfin, hfs⟩
      simp only [appCost_fn, List.cons_append, List.nil_append, List.foldl_cons, List.length_cons,
        List.length_nil] at h2 ⊢
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.lam0.costEq P
        (by includes)]
      have e1 : psi r shift (q :: l) = rk r shift q + psi r shift l := by simp [psi]
      rw [e1]
      have e2 : stepPrice r * (psi r shift basis.toList + (rk r shift q + psi r shift l)) =
          stepPrice r * (psi r shift basis.toList + rk r shift q) + stepPrice r * psi r shift l := by ring
      have e3 : stepPrice r * (psi r shift (insertKernelLeafRowIncremental basis shift q).toList +
          psi r shift l) = stepPrice r * psi r shift (insertKernelLeafRowIncremental basis shift q).toList +
          stepPrice r * psi r shift l := by ring
      have e4 : (incPrice r + 16) * (l.length + 1) = (incPrice r + 16) * l.length + incPrice r + 16 := by
        ring
      omega
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.reduceKernelLeafRowsIncremental.c526.costEq P hP]
  obtain ⟨h1, h2, h3⟩ := key rows.toList #[] (by simp [RowsInv]) (by simp) h
  have hred : reduceKernelLeafRowsIncremental rows shift =
      rows.toList.foldl (fun basis row ↦ insertKernelLeafRowIncremental basis shift row) #[] := by
    rw [reduceKernelLeafRowsIncremental, Array.foldl_toList]
  rw [hred]
  refine ⟨?_, h2, h3⟩
  have hp := psi_le r shift rows.toList
  have : stepPrice r * psi r shift rows.toList ≤ stepPrice r * (2 * r * rows.size) := by
    simp only [Array.length_toList] at hp
    exact Nat.mul_le_mul_left _ hp
  simp only [psi, List.map_nil, List.sum_nil, Nat.zero_add, Array.length_toList]
    at h1 this ⊢
  have e : (incPrice r + 19) * rows.size = (incPrice r + 16) * rows.size + 3 * rows.size := by ring
  omega

end

end LeanVM.Cost.Bounds.PMCore
