/-
  LeanVM.ToMathlib.Finset

  General sums over `Finset.range` Mathlib does not state, one home for each, in Mathlib's namespace
  and naming.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Finset

public section

variable {M : Type*} [AddCommMonoid M]

/-- A sum over `range (2 * n)` by its even and odd terms. -/
theorem sum_range_two_mul (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih, sum_range_succ,
      add_assoc]

/-- A sum over `range (a * b)` as `a` blocks of `b`. -/
theorem sum_range_mul (a b : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (a * b), f i = ∑ i ∈ range a, ∑ j ∈ range b, f (b * i + j) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ, Nat.mul_comm a b]

/-- A sum over `range (a * b)` as `b` blocks of `a`, the block index outside. -/
theorem sum_range_mul' (a b : ℕ) (f : ℕ → M) :
    ∑ i ∈ range (a * b), f i = ∑ j ∈ range b, ∑ i ∈ range a, f (i + a * j) := by
  rw [Nat.mul_comm, sum_range_mul]
  exact sum_congr rfl fun j _ ↦ sum_congr rfl fun i _ ↦ by rw [Nat.add_comm]

theorem sum_range_eq_sum_map_range (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range n, f i = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sum_range_succ, ih, List.range_succ, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]

end

end Finset
