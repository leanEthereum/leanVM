import Mathlib.LinearAlgebra.Lagrange

/-! An actual quadratic field-operation erasure interpolation evaluator. Correctness requires enough distinct authenticated evaluations of the same polynomial. It does not locate a common agreement set inside an adversarial word or decode errors. Inversion counts as one field operation; a machine refinement must charge its implementation separately. -/
namespace Whir.ErasureInterpolation
open Polynomial
open scoped BigOperators

variable {F I : Type*} [Field F]

/-- A product evaluator and its exact field-operation counter. Each factor uses two subtractions, one inversion, and two multiplications including multiplication into the accumulator. -/
def product (nodes : List F) (node point : F) : F × Nat :=
  match nodes with
  | [] => (1, 0)
  | other :: rest =>
    let result := product rest node point
    (((point - other) * (node - other)⁻¹) * result.1, result.2 + 5)

theorem product_value (nodes : List F) (node point : F) :
    (product nodes node point).1 =
      (nodes.map fun other => (point - other) * (node - other)⁻¹).prod := by
  induction nodes with
  | nil => rfl
  | cons other rest ih => simp [product, ih]

theorem product_operations (nodes : List F) (node point : F) :
    (product nodes node point).2 = 5 * nodes.length := by
  induction nodes with
  | nil => rfl
  | cons other rest ih => simp [product, ih, Nat.mul_add]

/-- The outer evaluator adds one multiply and one add per interpolation term. It receives explicit ordered lists, rather than using classical Finset enumeration. -/
def evaluate (indices : List I) (others : I → List F) (nodes values : I → F)
    (point : F) : F × Nat :=
  match indices with
  | [] => (0, 0)
  | index :: rest =>
    let basis := product (others index) (nodes index) point
    let result := evaluate rest others nodes values point
    (values index * basis.1 + result.1, basis.2 + result.2 + 2)

theorem evaluate_value (indices : List I) (others : I → List F) (nodes values : I → F)
    (point : F) :
    (evaluate indices others nodes values point).1 =
      (indices.map fun i => values i *
        ((others i).map fun other => (point - other) * (nodes i - other)⁻¹).prod).sum := by
  induction indices with
  | nil => rfl
  | cons index rest ih => simp [evaluate, product_value, ih]

/-- The counter follows the executable recursion; the bound is quadratic when each basis has at most `width` factors. -/
theorem evaluate_operations_le (indices : List I) (others : I → List F)
    (nodes values : I → F) (point : F) (width : Nat)
    (lengths : ∀ i ∈ indices, (others i).length ≤ width) :
    (evaluate indices others nodes values point).2 ≤ indices.length * (5 * width + 2) := by
  induction indices with
  | nil => simp [evaluate]
  | cons index rest ih =>
    have tail := ih (fun i hi => lengths i (by simp [hi]))
    have head := lengths index (by simp)
    simp only [evaluate, product_operations, List.length_cons, Nat.add_mul]
    omega

/-- The supplied lists are certified enumerations of the actual interpolation set. They are computational inputs; the proof does not choose or search for an agreement set. -/
theorem evaluate_interpolates [DecidableEq I]
    (records : Finset I) (indices : List I) (others : I → List F)
    (nodes values : I → F) (point : F)
    (enumeration : (indices : Multiset I) = records.val)
    (basisEnumeration : ∀ i ∈ records,
      (others i : Multiset F) = (records.erase i).val.map nodes) :
    (evaluate indices others nodes values point).1 =
      (Lagrange.interpolate records nodes values).eval point := by
  rw [evaluate_value, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_multiset_sum, ← enumeration]
  change ((indices : Multiset I).map _).sum = ((indices : Multiset I).map _).sum
  apply congrArg Multiset.sum
  apply Multiset.map_congr rfl
  intro i hi
  have member : i ∈ records := by
    change i ∈ records.val
    rw [← enumeration]
    exact hi
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.basis,
    Polynomial.eval_prod, Lagrange.basisDivisor, Polynomial.eval_sub,
    Polynomial.eval_X]
  rw [Finset.prod_eq_multiset_prod]
  congr 1
  change ((others i : Multiset F).map _).prod = _
  rw [basisEnumeration i member, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro j hj
  exact mul_comm _ _

/-- With at least the degree threshold of distinct correct rows, the implemented evaluator recovers every evaluation of the actual polynomial. -/
theorem evaluate_recovers [DecidableEq I]
    (records : Finset I) (indices : List I) (others : I → List F)
    (nodes values : I → F) (point : F) (p : F[X])
    (enumeration : (indices : Multiset I) = records.val)
    (basisEnumeration : ∀ i ∈ records,
      (others i : Multiset F) = (records.erase i).val.map nodes)
    (distinct : Set.InjOn nodes records) (enough : p.degree < records.card)
    (correct : ∀ i ∈ records, p.eval (nodes i) = values i) :
    (evaluate indices others nodes values point).1 = p.eval point := by
  rw [evaluate_interpolates records indices others nodes values point enumeration basisEnumeration,
    ← Lagrange.eq_interpolate_of_eval_eq values distinct enough correct]

end Whir.ErasureInterpolation
