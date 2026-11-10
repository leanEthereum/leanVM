module

public import LeanVM.Cost.Extractor.PMCore
public import LeanVM.Cost.Bounds.Decoder.Rows
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Degree
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.Univariate.Raw.Core

/-!
# Bounds: the PM-basis node's glue, compiled

The compiled helpers of the PM-basis recursion (`Cost/Extractor/PMCore.lean`) besides its two
matrix products and its leaf, each for every program holding its bodies:

* `maxOrderC_cost` (`21·|orders| + 9`), `lowerOrdersC_cost` (`25·|orders| + 11`),
  `residualOrdersC_cost` (`21·|orders| + 11`): the folds and maps over the orders;
* `divXTruncC_cost` (`58·order + 33`): one residual entry;
* `updateShiftByRowsC_cost` (`(84·C + 63)·R + 19`): the shift update, `R` rows of at most `C`
  entries (`rowShiftedDegree_cost`: a constant per entry);
* `compactNonzeroRowsC_cost` (`((3·D + 33)·C + 30)·R + 8`): the zero-row filter, `R` rows of at
  most `C` entries of at most `D` coefficients (the zero test reads an entry's coefficients).

`PolynomialMatrix.ofFn` and `MatrixWidth` are bounded in `Bounds/Decoder/Rows.lean`
(`ofFnC_cost`, `matrixWidthC_cost`).

Word-sized orders, shifts, sizes throughout.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable (P : MachineProgram)

/-! ## Helpers -/

theorem le_maxOrder (problem : XAdicProblem K) : ∀ x ∈ problem.orders, x ≤ maxOrder problem := by
  intro x hx
  unfold maxOrder
  rw [← Array.foldl_toList]
  have hx' : x ∈ problem.orders.toList := by simpa using hx
  suffices h : ∀ (l : List ℕ) (a : ℕ), x ∈ l → x ≤ l.foldl max a from h _ 0 hx'
  intro l
  induction l with
  | nil => intro a h; simp at h
  | cons y l ih =>
    intro a h
    simp only [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have : ∀ (l : List ℕ) (b : ℕ), b ≤ l.foldl max b := by
        intro l; induction l with
        | nil => intro b; simp
        | cons z l ih' => intro b; exact (le_max_left b z).trans (ih' _)
      exact (le_max_right a x).trans (this l _)
    · exact ih _ h

theorem natDegree_le_size_sub_one' (q : CPolynomial K) : q.natDegree ≤ q.val.size - 1 := by
  unfold CPolynomial.natDegree
  split <;> omega

theorem getD_le_of_mem {a : Array ℕ} {B j : ℕ} (h : ∀ x ∈ a, x ≤ B) : a.getD j 0 ≤ B := by
  rw [Array.getD_eq_getD_getElem?]
  cases hj : a[j]? with
  | none => simp
  | some x => exact h x (Array.mem_of_getElem? hj)

/-! ## The orders -/

/-- **`maxOrder`** (`maxOrderC`): at most `21·|orders| + 9`, word-sized orders. -/
theorem maxOrderC_cost (hP : Includes P maxOrderC.costDeps) (problem : XAdicProblem K)
    (h : ∀ x ∈ problem.orders, x < 2 ^ 63) :
    machineCost P maxOrderC.costIdx [encodeValue problem] ≤ 21 * problem.orders.size + 9 := by
  rw [maxOrderC.costEq P hP]
  have hf := listFoldl_le P (by includes) (fun a b : ℕ ↦ max a b) (.closure maxOrderC.lam0.costIdx [])
    (fun a b ↦ RunsApp.of_spec (maxOrderC.lam0.costSpec P (by includes) a b)) 7
    (fun acc ↦ acc < 2 ^ 63) problem.orders.toList 0 (by norm_num)
    (fun acc hacc b hb ↦ ⟨by have := h b (by simpa using hb); omega, by
      rw [appCost_fn, List.nil_append, maxOrderC.lam0.costEq P (by includes),
        limbs_of_lt (by omega : acc < 2 ^ 64),
        limbs_of_lt (by have := h b (by simpa using hb); omega : b < 2 ^ 64)]
      simp⟩)
  simp only [Array.length_toList] at hf
  omega

/-- **`lowerOrders`** (`lowerOrdersC`): at most `25·|orders| + 11`. -/
theorem lowerOrdersC_cost (hP : Includes P lowerOrdersC.costDeps) (problem : XAdicProblem K)
    (d : ℕ) (hd : d < 2 ^ 64) (h : ∀ x ∈ problem.orders, x < 2 ^ 64) :
    machineCost P lowerOrdersC.costIdx [encodeValue problem, encodeValue d] ≤
      25 * problem.orders.size + 11 := by
  rw [lowerOrdersC.costEq P hP]
  have hm := map_cost P (by includes) (fun order : ℕ ↦ min order d)
    (.closure lowerOrdersC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (lowerOrdersC.lam0.costSpec P (by includes) d a)) 8
    problem.orders.toList (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, lowerOrdersC.lam0.costEq P (by includes),
        limbs_of_lt (h a (by simpa using ha)), limbs_of_lt hd]
      simp)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-- **`residualOrders`** (`residualOrdersC`): at most `21·|orders| + 11`. -/
theorem residualOrdersC_cost (hP : Includes P residualOrdersC.costDeps) (problem : XAdicProblem K)
    (d : ℕ) (hd : d < 2 ^ 64) (h : ∀ x ∈ problem.orders, x < 2 ^ 64) :
    machineCost P residualOrdersC.costIdx [encodeValue problem, encodeValue d] ≤
      21 * problem.orders.size + 11 := by
  rw [residualOrdersC.costEq P hP]
  have hm := map_cost P (by includes) (fun order : ℕ ↦ order - d)
    (.closure residualOrdersC.lam0.costIdx [encodeValue d])
    (fun a ↦ RunsApp.of_spec (residualOrdersC.lam0.costSpec P (by includes) d a)) 4
    problem.orders.toList (fun a ha ↦ by
      rw [appCost_fn, List.singleton_append, residualOrdersC.lam0.costEq P (by includes),
        limbs_of_lt (h a (by simpa using ha)), limbs_of_lt hd]
      simp)
  simp only [Array.length_toList, List.length_map] at hm ⊢
  omega

/-! ## One residual entry -/

/-- **`divXTrunc shift order p`** (`divXTruncC`): at most `58·order + 33`. -/
theorem divXTruncC_cost (hP : Includes P divXTruncC.costDeps) (shift order : ℕ)
    (p : CPolynomial K) (h : shift + order < 2 ^ 63) :
    machineCost P divXTruncC.costIdx [encodeValue shift, encodeValue order, encodeValue p] ≤
      58 * order + 33 := by
  rw [divXTruncC.costEq P hP]
  have hr := rangeLoop_cost P (by includes) order [] (by omega)
  have hm := map_cost P (by includes) (fun i ↦ p.coeff (i + shift))
    (.closure divXTruncC.lam0.costIdx [encodeValue shift, encodeValue p])
    (fun a ↦ RunsApp.of_spec (divXTruncC.lam0.costSpec P (by includes) shift p a)) 8
    (List.range order) (fun a ha ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        divXTruncC.lam0.costEq P (by includes)]
      have := List.mem_range.1 ha
      cost_simp
      omega)
  have ho := ofArray_cost P (by includes)
    (List.map (fun i ↦ p.coeff (i + shift)) (List.range order)).toArray (by simp; omega)
  simp only [List.length_range, List.length_map, List.size_toArray] at hm ho ⊢
  omega

/-! ## The shift update and the zero-row filter -/

/-- **`updateShiftByRows`** (`updateShiftByRowsC`): `R` rows of at most `C` entries of at most
`D` coefficients, shifts at most `S`: at most `(84·C + 63)·R + 19`. -/
theorem updateShiftByRowsC_cost (hP : Includes P updateShiftByRowsC.costDeps)
    {C D S : ℕ} (hC : C < 2 ^ 62) (hDS : D + S < 2 ^ 62) (basis : PolynomialMatrix K)
    (hR : basis.size < 2 ^ 62) (hrows : ∀ i, RowWithin C D (basis.getD i #[]))
    (shift : Array ℕ) (hS : ∀ j, shift.getD j 0 ≤ S) :
    machineCost P updateShiftByRowsC.costIdx [encodeValue basis, encodeValue shift] ≤
      (84 * C + 63) * basis.size + 19 := by
  rw [updateShiftByRowsC.costEq P hP]
  have hr := rangeLoop_cost P (by includes) basis.size [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure updateShiftByRowsC.lam0.costIdx [encodeValue basis, encodeValue shift])
    (fun a ↦ RunsApp.of_spec (updateShiftByRowsC.lam0.costSpec P (by includes) basis shift a))
    (84 * C + 33) (List.range basis.size) (fun a _ ↦ by
      rw [appCost_fn, List.cons_append, List.cons_append, List.nil_append,
        updateShiftByRowsC.lam0.costEq P (by includes)]
      have := rowShiftedDegree_cost P (by includes) hC hDS (basis.getD a #[]) (hrows a) shift hS
      cases rowShiftedDegree? (basis.getD a #[]) shift <;> dsimp only <;> cost_simp <;> omega)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

/-- The zero test of one entry: at most `3·|p| + 19`. -/
theorem rowIsZeroLam_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.lam0.costDeps)
    (p : CPolynomial K) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.lam0.costIdx [encodeValue p] ≤
      3 * p.val.size + 19 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.lam0.costEq P hP]
  have h0 : (0 : CPolynomial K).val.size = 0 := rfl
  have hl : (0 : CPolynomial K).val.toList = [] := rfl
  rw [h0, hl]
  cases hq : p.val.toList with
  | nil => rw [Auto.List.beq.c5.costEq_nil P (by includes)]; simp
  | cons x l => rw [Auto.List.beq.c5.costEq_cons P (by includes)]; simp

/-- **`rowIsZero`**: a row of at most `C` entries of at most `D` coefficients, at most
`(3·D + 33)·C + 7`. -/
theorem rowIsZeroC_cost (hP : Includes P Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.costDeps)
    {C D : ℕ} (row : PolynomialRow K) (h : RowWithin C D row) :
    machineCost P Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.costIdx [encodeValue row] ≤
      (3 * D + 33) * C + 7 := by
  rw [Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.costEq P hP]
  have ha := all_cost P (by includes) (fun p : CPolynomial K ↦ p == 0)
    (.closure Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.rowIsZero.c476.lam0.costSpec P (by includes) a))
    (3 * D + 19) row.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil]
      have := rowIsZeroLam_cost P (by includes) a
      have := h.2 a (by simpa using ha)
      omega)
  have hs := h.1
  simp only [Array.length_toList] at ha
  have : (3 * D + 19 + 11) * row.size ≤ (3 * D + 30) * C := Nat.mul_le_mul_left _ hs
  nlinarith

/-- **`compactNonzeroRows`** (`compactNonzeroRowsC`): `R` rows of at most `C` entries of at most
`D` coefficients, at most `((3·D + 33)·C + 30)·R + 8`. -/
theorem compactNonzeroRowsC_cost (hP : Includes P compactNonzeroRowsC.costDeps)
    {C D : ℕ} (rows : PolynomialMatrix K) (h : ∀ row ∈ rows.toList, RowWithin C D row) :
    machineCost P compactNonzeroRowsC.costIdx [encodeValue rows] ≤
      ((3 * D + 33) * C + 30) * rows.size + 8 := by
  rw [compactNonzeroRowsC.costEq P hP]
  have hf := filter_cost P (by includes) (fun row ↦ !rowIsZero row)
    (.closure compactNonzeroRowsC.lam0.costIdx [])
    (fun a ↦ RunsApp.of_spec (compactNonzeroRowsC.lam0.costSpec P (by includes) a))
    ((3 * D + 33) * C + 11) rows.toList (fun a ha ↦ by
      rw [appCost_fn, List.nil_append, List.length_nil, compactNonzeroRowsC.lam0.costEq P (by includes)]
      have := rowIsZeroC_cost P (by includes) a (h a ha)
      omega)
  have hl := List.length_filter_le (fun row ↦ !rowIsZero row) rows.toList
  simp only [Array.length_toList] at hf hl
  nlinarith

/-! ## `PolynomialMatrix.ofFn` -/

end

end LeanVM.Cost.Bounds.PMCore
