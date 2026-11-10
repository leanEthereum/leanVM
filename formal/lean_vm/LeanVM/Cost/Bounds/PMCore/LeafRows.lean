module

public import LeanVM.Cost.Bounds.PMCore.LeafKernel
import all CompPoly.LinearAlgebra.PolynomialMatrix.Approximant.PMBasis.KernelLeaf
import all CompPoly.LinearAlgebra.PolynomialMatrix.Basic
import all CompPoly.Univariate.Basic

/-!
# Bounds: the leaf's coefficient rows, compiled

The order-one leaf's scalar system (CompPoly, `KernelLeaf.lean`): the equation indices
(`coefficientEquationIndices`, nested `for` loops, `E ≤ m` of them when every order is at most
one: **`coefficientEquationIndicesC_cost`**, `m² + 160·m + 64`) and the coefficient rows
(`coefficientMatrixRows`, `E` rows of `n·cap` coefficients: **`coefficientMatrixRowsC_cost`**).
-/

namespace LeanVM.Cost.Bounds.PMCore

open LeanVM.Cost LeanVM.Cost.Bounds LeanVM.Cost.Library LeanVM.Cost.Extractor LeanVM.Parameters
open LeanVM.Cost.Bounds.Decoder CompPoly CompPoly.PolynomialMatrix CompPoly.PolynomialMatrix.Approximant
open LeanVM.Cost.LoopLib

public section

/-! ## `for` loops in `Id` -/

/-- A loop whose steps grow a size by at most `g` grows it by at most `g` per element. -/
theorem listForInId_size {β : Type} (f : ℕ → β → ForInStep β) (sz : β → ℕ) (g : ℕ)
    (hf : ∀ a s, sz (match f a s with | .done y => y | .yield y => y) ≤ sz s + g) :
    ∀ (l : List ℕ) (s : β), sz (listForInId f l s) ≤ sz s + g * l.length := by
  intro l
  induction l with
  | nil => intro s; simp [listForInId]
  | cons a l ih =>
    intro s
    have h1 := hf a s
    rw [listForInId]
    cases hfa : f a s with
    | done y => simp only [hfa] at h1; simp only [List.length_cons]; nlinarith
    | yield y =>
      simp only [hfa] at h1
      have := ih y
      simp only [List.length_cons]
      nlinarith

variable (P : MachineProgram)

/-- **A `for` loop in `Id`** (`listForInId`): each step at most `sz acc + C`, growing `sz` by at
most `g`: at most `|l|·(sz acc + g·|l| + C + 14) + 3`. -/
theorem listForInIdC_cost (hP : Includes P Auto.LeanVM.Cost.LoopLib.listForInId.c519.costDeps)
    {β : Type} [MachineEncoding β] (f : ℕ → β → ForInStep β) (fVal : MachineValue)
    (hf : ∀ (a : ℕ) (b : β), RunsApp P fVal [encodeValue a, encodeValue b] (encodeValue (f a b)))
    (sz : β → ℕ) (g C : ℕ)
    (hg : ∀ a s, sz (match f a s with | .done y => y | .yield y => y) ≤ sz s + g)
    (hC : ∀ (a : ℕ) (s : β), appCost P fVal [encodeValue a, encodeValue s] ≤ sz s + C) :
    ∀ (l : List ℕ) (s : β),
      machineCost P Auto.LeanVM.Cost.LoopLib.listForInId.c519.costIdx
        [fVal, encodeValue l, encodeValue s] ≤
        l.length * (sz s + g * l.length + C + 14) + 3 := by
  intro l
  induction l with
  | nil => intro s; rw [Auto.LeanVM.Cost.LoopLib.listForInId.c519.costEq P hP f fVal hf]; simp
  | cons a l ih =>
    intro s
    rw [Auto.LeanVM.Cost.LoopLib.listForInId.c519.costEq P hP f fVal hf]
    have h1 := hC a s
    have h2 := hg a s
    simp only [List.length_cons]
    cases hfa : f a s with
    | done y =>
      have h3 : sz s + C + 14 ≤ sz s + g * (l.length + 1) + C + 14 := by omega
      have h4 := Nat.le_mul_of_pos_left (sz s + g * (l.length + 1) + C + 14)
        (show 0 < l.length + 1 by omega)
      dsimp only
      omega
    | yield y =>
      dsimp only
      simp only [hfa] at h2
      have := ih y
      have e : (l.length + 1) * (sz s + g * (l.length + 1) + C + 14) ≥
          l.length * (sz y + g * l.length + C + 14) + sz s + C + 14 := by nlinarith
      omega

/-! ## The equation indices -/

theorem rangeSize_cost (hP : Includes P Auto.Std.Legacy.Range.size.c522.costDeps) (n : ℕ)
    (hn : n < 2 ^ 62) :
    machineCost P Auto.Std.Legacy.Range.size.c522.costIdx [encodeValue [:n]] ≤ 17 := by
  rw [Auto.Std.Legacy.Range.size.c522.costEq P hP]
  rw [limbs_of_lt (by omega : n < 2 ^ 64), limbs_of_lt (by omega : n - 0 < 2 ^ 64),
    limbs_of_lt (by omega : n - 0 + 1 < 2 ^ 64), limbs_of_lt (by omega : n - 0 + 1 - 1 < 2 ^ 64)]
  simp

theorem rangeSize_eq (n : ℕ) : [:n].size = n := by simp [Std.Legacy.Range.size]

/-- The inner loop's body. -/
@[expose] def eqInner (j : ℕ) : ℕ → Array (ℕ × ℕ) → ForInStep (Array (ℕ × ℕ)) :=
  fun t s ↦ .yield (s.push (j, t))

/-- The outer loop's body. -/
@[expose] def eqOuter (orders : Array ℕ) : ℕ → Array (ℕ × ℕ) → ForInStep (Array (ℕ × ℕ)) :=
  fun j s ↦ .yield (listForInId (eqInner j) (List.range' 0 (orders.getD j 0) 1) s)

theorem eqOuter_size (orders : Array ℕ) (h : ∀ j, orders.getD j 0 ≤ 1) (j : ℕ) (s : Array (ℕ × ℕ)) :
    (match eqOuter orders j s with | .done y => y | .yield y => y).size ≤ s.size + 1 := by
  simp only [eqOuter]
  have := listForInId_size (eqInner j) Array.size 1
    (fun a s ↦ by simp [eqInner]) (List.range' 0 (orders.getD j 0) 1) s
  simp only [List.length_range'] at this
  have := h j
  omega

theorem coefficientEquationIndices_eq (orders : Array ℕ) :
    coefficientEquationIndices orders = listForInId (eqOuter orders) (List.range' 0 orders.size 1) #[] := by
  unfold coefficientEquationIndices
  simp only [Id.run, forIn_range_id, rangeSize_eq]
  rfl

/-- **The equations of an order-one leaf**: at most `m` of them. -/
theorem coefficientEquationIndices_size_le (orders : Array ℕ) (h : ∀ j, orders.getD j 0 ≤ 1) :
    (coefficientEquationIndices orders).size ≤ orders.size := by
  rw [coefficientEquationIndices_eq]
  have := listForInId_size (eqOuter orders) Array.size 1 (eqOuter_size orders h)
    (List.range' 0 orders.size 1) #[]
  simpa using this

/-- **The equation indices** (`coefficientEquationIndices`), orders at most one: at most
`m² + 151·m + 63`, `m` the orders. -/
theorem coefficientEquationIndicesC_cost
    (hP : Includes P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.costDeps)
    (orders : Array ℕ) (h : ∀ j, orders.getD j 0 ≤ 1) (hm : orders.size < 2 ^ 30) :
    machineCost P Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.costIdx
        [encodeValue orders] ≤ orders.size * orders.size + 151 * orders.size + 63 := by
  rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.costEq P hP]
  have hs := rangeSize_cost P (by includes) orders.size (by omega)
  simp only [rangeSize_eq]
  have hr := rangeC_cost P (by includes) orders.size 0 (by omega)
  have hfo := fun a b ↦ RunsApp.of_spec (us := [encodeValue orders]) (vs := [encodeValue a, encodeValue b])
    (Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.costSpec P
      (by includes) orders a b)
  have hloop := listForInIdC_cost P (by includes) _
    (.closure Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.costIdx
      [encodeValue orders]) hfo
    Array.size 1 119 (fun j s ↦ by
      have hj := h j
      have e : orders[j]?.getD 0 = orders.getD j 0 := (Array.getD_eq_getD_getElem? ..).symm
      simp
      simp only [pure]
      simp
      omega) (fun j s ↦ by
      simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
      rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.costEq P
        (by includes)]
      have hj := h j
      have hs' := rangeSize_cost P (by includes) (orders.getD j 0) (by omega)
      simp only [rangeSize_eq]
      have hr' := rangeC_cost P (by includes) (orders.getD j 0) 0 (by omega)
      have hfi := fun a b ↦ RunsApp.of_spec (us := [encodeValue j]) (vs := [encodeValue a, encodeValue b])
        (Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.lam0.costSpec P
          (by includes) j a b)
      have hin := listForInIdC_cost P (by includes) _
        (.closure Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.lam0.costIdx
          [encodeValue j]) hfi
        Array.size 1 15 (fun a s ↦ by simp only [pure]; simp) (fun a s ↦ by
          simp only [appCost_fn, List.cons_append, List.nil_append, List.length_cons, List.length_nil]
          rw [Auto.CompPoly.PolynomialMatrix.Approximant.coefficientEquationIndices.c518.lam0.lam0.costEq P
            (by includes)])
        (List.range' 0 (orders.getD j 0) 1) s
      simp only [List.length_range'] at hin
      have : orders.getD j 0 * (s.size + 1 * orders.getD j 0 + 15 + 14) ≤ s.size + 30 := by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hj with h0 | h1
        · rw [h0]; omega
        · rw [h1]; omega
      omega) (List.range' 0 orders.size 1) #[]
  simp only [List.length_range', Array.size_empty] at hloop
  have : orders.size * (0 + 1 * orders.size + 119 + 14) = orders.size * orders.size + 133 * orders.size := by
    ring
  omega

end

end LeanVM.Cost.Bounds.PMCore
