module

public import LeanVM.Cost.Bounds.PMCore.LeafRows
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeafSoundness

/-!
# Bounds: the leaf's small pieces, compiled

`leafDegreeCap`, `coeffXPower`, `monomialUnitRow`, `kernelLeafCompletionRows`,
`vectorToPolynomialRow`, `coefficientMatrixRow(s)` (CompPoly, `KernelLeaf.lean`) and the slot table
of the leaf sorted by pivot (`slotTable`, `fillPivotSlots`, `Fast/PMBasis/PopovLeaf.lean`), at
cap `c`, `n` rows, `m` orders.
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant

public section

variable (P : MachineProgram)

/-- `leafDegreeCap`: at most `42·|orders| + 27`. -/
theorem leafDegreeCapC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.leafDegreeCap.c490.costDeps)
    (problem : XAdicProblem K) (h : ∀ x ∈ problem.orders, x < 2 ^ 63) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.leafDegreeCap.c490.costIdx
        [encodeValue problem] ≤ 42 * problem.orders.size + 27 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.leafDegreeCap.c490.costEq P hP]
  have := maxOrderC_cost P (by includes) problem h
  have hmo : maxOrder problem < 2 ^ 63 := by
    unfold maxOrder
    rw [← Array.foldl_toList]
    have key : ∀ (l : List ℕ) (a : ℕ), a < 2 ^ 63 → (∀ x ∈ l, x < 2 ^ 63) → l.foldl max a < 2 ^ 63 := by
      intro l
      induction l with
      | nil => intro a ha _; exact ha
      | cons x l ih =>
        intro a ha hl
        exact ih _ (by have := hl x (by simp); omega) (fun y hy ↦ hl y (by simp [hy]))
    exact key _ 0 (by norm_num) (fun x hx ↦ h x (by simpa using hx))
  rw [limbs_of_lt (by omega : maxOrder problem < 2 ^ 64)]
  split_ifs <;> omega

/-- `coeffXPower c d` (`c·X^d`): at most `23·d + 42`. -/
theorem coeffXPowerC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.coeffXPower.c489.costDeps)
    (c : K) (d : ℕ) (hd : d < 2 ^ 62) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.coeffXPower.c489.costIdx
        [encodeValue c, encodeValue d] ≤ 23 * d + 42 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.coeffXPower.c489.costEq P hP]
  have := ofArray_cost P (by includes) ((Array.replicate d (0 : K)).push c) (by simp; omega)
  simp only [Array.size_replicate, Array.size_push] at this ⊢
  omega

/-- `monomialUnitRow w i d` (`X^d·eᵢ`): at most `(23·d + 80)·w + 18`. -/
theorem monomialUnitRowC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.costDeps)
    (w i d : ℕ) (hw : w < 2 ^ 62) (hi : i < 2 ^ 64) (hd : d < 2 ^ 62) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.costIdx
        [encodeValue w, encodeValue i, encodeValue d] ≤ (23 * d + 80) * w + 18 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.costEq P hP]
  have hr := rangeLoop_cost P (by includes) w [] (by omega)
  have hm := map_cost P (by includes)
    (fun j ↦ if (i == j) = true then coeffXPower (1 : K) d else 0)
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.lam0.costIdx
      [encodeValue i, encodeValue d])
    (fun a ↦ RunsApp.of_spec (Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.lam0.costSpec P
      (by includes) i d a)) (23 * d + 51) (List.range w) (fun j hj ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.monomialUnitRow.c487.lam0.costEq P (by includes),
        limbs_of_lt hi, limbs_of_lt (by have := List.mem_range.1 hj; omega : j < 2 ^ 64)]
      have := coeffXPowerC_cost P (by includes) 1 d hd
      split_ifs <;> simp only [max_self] <;> omega)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

theorem size_monomialUnitRow (n i d : ℕ) : (monomialUnitRow (F := K) n i d).size = n := by
  simp [monomialUnitRow]

theorem size_coeffXPower (c : K) (d : ℕ) : (coeffXPower c d).val.size ≤ d + 1 := by
  have := ofArray_size_le ((Array.replicate d (0 : K)).push c)
  simpa [coeffXPower] using this

theorem rowWithin_monomialUnitRow (n i : ℕ) : RowWithin n 2 (monomialUnitRow (F := K) n i 1) := by
  refine ⟨(size_monomialUnitRow n i 1).le, fun e he ↦ ?_⟩
  simp only [monomialUnitRow, List.mem_toArray, List.mem_map, List.mem_range] at he
  obtain ⟨j, -, rfl⟩ := he
  split_ifs
  · exact size_coeffXPower 1 1
  · simp [size_zero_val]

/-- **The completion rows** (`kernelLeafCompletionRows`), `n` rows at cap `c`: at most
`42·|orders| + ((23·c + 80)·n + 39)·n + 16·n + 50`. -/
theorem completionRowsC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.costDeps)
    (problem : XAdicProblem K) (h : ∀ x ∈ problem.orders, x < 2 ^ 63) (hn : problem.matrix.size < 2 ^ 30)
    (hc : leafDegreeCap problem < 2 ^ 30) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.costIdx
        [encodeValue problem] ≤
      42 * problem.orders.size +
        ((23 * leafDegreeCap problem + 80) * problem.matrix.size + 39) * problem.matrix.size +
          16 * problem.matrix.size + 50 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.costEq P hP]
  have := leafDegreeCapC_cost P (by includes) problem h
  have hr := rangeLoop_cost P (by includes) problem.matrix.size [] (by omega)
  have hm := map_cost P (by includes)
    (fun i ↦ monomialUnitRow problem.matrix.size i (leafDegreeCap problem))
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.lam0.costIdx
      [encodeValue problem, encodeValue (leafDegreeCap problem)])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.lam0.costSpec P
        (by includes) problem (leafDegreeCap problem) a))
    ((23 * leafDegreeCap problem + 80) * problem.matrix.size + 26) (List.range problem.matrix.size)
    (fun i hi ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.kernelLeafCompletionRows.c545.lam0.costEq P
        (by includes)]
      have := monomialUnitRowC_cost P (by includes) problem.matrix.size i (leafDegreeCap problem)
        (by omega) (by have := List.mem_range.1 hi; omega) (by omega)
      omega)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

/-- `vectorToPolynomialRow c w v`: at most `(61·c + 66)·w + 18`. -/
theorem vectorToPolynomialRowC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.costDeps)
    (c w : ℕ) (v : Array K) (hc : c < 2 ^ 30) (hw : w < 2 ^ 30) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.costIdx
        [encodeValue c, encodeValue w, encodeValue v] ≤ (61 * c + 66) * w + 18 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.costEq P hP]
  have hr := rangeLoop_cost P (by includes) w [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.costIdx
      [encodeValue c, encodeValue v])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.costSpec P
        (by includes) c v a)) (61 * c + 37) (List.range w) (fun coord hcoord ↦ by
      have hco := List.mem_range.1 hcoord
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.costEq P
        (by includes)]
      have hr' := rangeLoop_cost P (by includes) c [] (by omega)
      have hm' := map_cost P (by includes) _
        (.closure Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.lam0.costIdx
          [encodeValue c, encodeValue v, encodeValue coord])
        (fun a ↦ RunsApp.of_spec
          (Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.lam0.costSpec P
            (by includes) c v coord a)) 11 (List.range c) (fun d hd ↦ by
          have hd' := List.mem_range.1 hd
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.CompPoly.PolynomialMatrix.Approximant.vectorToPolynomialRow.c493.lam0.lam0.costEq P
            (by includes), limbs_of_lt (by omega : coord < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64),
            limbs_of_lt (by omega : d < 2 ^ 64),
            limbs_of_lt (show coord * c < 2 ^ 64 by
              have := Nat.mul_le_mul (show coord ≤ 2 ^ 30 by omega) (show c ≤ 2 ^ 30 by omega)
              omega),
            limbs_of_lt (show coord * c + d < 2 ^ 64 by
              have := Nat.mul_le_mul (show coord ≤ 2 ^ 30 by omega) (show c ≤ 2 ^ 30 by omega)
              omega)]
          simp)
      have ho := ofArray_cost P (by includes)
        (List.map (fun degree ↦ v.getD (coord * c + degree) 0) (List.range c)).toArray (by simp; omega)
      simp only [List.length_range, List.length_map, List.size_toArray] at hm' ho ⊢
      omega)
  simp only [List.length_range, List.length_map] at hm ⊢
  nlinarith

/-- `coefficientMatrixRow problem c eq`: at most `70·n·c + 24`. -/
theorem coefficientMatrixRowC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.costDeps)
    (problem : XAdicProblem K) (c : ℕ) (eq : ℕ × ℕ) (hn : problem.matrix.size < 2 ^ 30)
    (hc : 1 ≤ c) (hc' : c < 2 ^ 30) (heq : eq.2 < 2 ^ 63) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.costIdx
        [encodeValue problem, encodeValue c, encodeValue eq] ≤ 70 * (problem.matrix.size * c) + 24 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.costEq P hP]
  have hnc : problem.matrix.size * c ≤ 2 ^ 60 := by
    have := Nat.mul_le_mul (show problem.matrix.size ≤ 2 ^ 30 by omega) (show c ≤ 2 ^ 30 by omega)
    omega
  have hr := rangeLoop_cost P (by includes) (problem.matrix.size * c) [] (by omega)
  have hm := map_cost P (by includes) _
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.lam0.costIdx
      [encodeValue problem, encodeValue c, encodeValue eq])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.lam0.costSpec P
        (by includes) problem c eq a)) 41 (List.range (problem.matrix.size * c)) (fun col hcol ↦ by
      have hco := List.mem_range.1 hcol
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRow.c517.lam0.costEq P
        (by includes), limbs_of_lt (by omega : col < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64),
        limbs_of_lt (by have := Nat.mod_lt col (show c > 0 by omega); omega : col % c < 2 ^ 64),
        limbs_of_lt (by omega : eq.2 < 2 ^ 64), rowGet_cost P (by includes)]
      split_ifs <;> simp only [max_self] <;> omega)
  rw [limbs_of_lt (by omega : problem.matrix.size < 2 ^ 64), limbs_of_lt (by omega : c < 2 ^ 64),
    limbs_of_lt (by omega : problem.matrix.size * c < 2 ^ 64)]
  simp only [List.length_range, List.length_map] at hm ⊢
  omega

theorem coefficientMatrixRows_shape (problem : XAdicProblem K) :
    RowsWithin (coefficientEquationIndices problem.orders).size
      (problem.matrix.size * leafDegreeCap problem) (coefficientMatrixRows problem) := by
  refine ⟨by simp [coefficientMatrixRows], fun i ↦ ?_⟩
  rcases Nat.lt_or_ge i (coefficientMatrixRows problem).size with hi | hi
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    simp [coefficientMatrixRows, coefficientMatrixRow]
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hi]; simp

/-- **The coefficient rows** (`coefficientMatrixRows`), orders at most one, cap `c = 1`. -/
theorem coefficientMatrixRowsC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.costDeps)
    (problem : XAdicProblem K) (h1 : maxOrder problem ≤ 1) (hn : problem.matrix.size < 2 ^ 30)
    (hm : problem.orders.size < 2 ^ 30) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.costIdx
        [encodeValue problem] ≤
      42 * problem.orders.size + 27 +
        (problem.orders.size * problem.orders.size + 151 * problem.orders.size + 63) +
        (70 * problem.matrix.size + 47) * problem.orders.size + 17 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.costEq P hP]
  have hord : ∀ x ∈ problem.orders, x ≤ 1 := fun x hx ↦ (le_maxOrder problem x hx).trans h1
  have hcap : leafDegreeCap problem = 1 := LeanVM.Extraction.Fast.PMDegree.leafDegreeCap_eq_one h1
  have hl := leafDegreeCapC_cost P (by includes) problem (fun x hx ↦ by have := hord x hx; omega)
  have hord' : ∀ j, problem.orders.getD j 0 ≤ 1 := fun j ↦ getD_le_of_mem hord
  have he := coefficientEquationIndicesC_cost P (by includes) problem.orders hord' hm
  have hE := coefficientEquationIndices_size_le problem.orders hord'
  have hmap := map_cost P (by includes) (coefficientMatrixRow problem (leafDegreeCap problem))
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.lam0.costIdx
      [encodeValue problem, encodeValue (leafDegreeCap problem)])
    (fun a ↦ RunsApp.of_spec
      (Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.lam0.costSpec P
        (by includes) problem (leafDegreeCap problem) a)) (70 * problem.matrix.size + 30)
    (coefficientEquationIndices problem.orders).toList (fun eq heq ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientMatrixRows.c515.lam0.costEq P
        (by includes)]
      have hb := mem_coefficientEquationIndices_bounds (orders := problem.orders) (j := eq.1)
        (t := eq.2) (by simpa using heq)
      have := hord' eq.1
      have := coefficientMatrixRowC_cost P (by includes) problem (leafDegreeCap problem) eq hn
        (by omega) (by omega) (by omega)
      have e : problem.matrix.size * leafDegreeCap problem = problem.matrix.size := by
        rw [hcap, Nat.mul_one]
      omega)
  simp only [Array.length_toList, List.length_map] at hmap ⊢
  have e : (70 * problem.matrix.size + 30 + 13) * (coefficientEquationIndices problem.orders).size ≤
      (70 * problem.matrix.size + 43) * problem.orders.size := Nat.mul_le_mul_left _ hE
  nlinarith

end

end LeanVM.Cost.Bounds.PMCore
