/-
  LeanVM.ToMathlib.Finset

  Finset sum lemmas the proofs share that Mathlib does not state.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Sums over ranges

A sum over `range (2 * n)` split into its even and odd terms, in Mathlib's namespace and naming, as
a candidate for upstreaming.
-/

namespace Finset

@[expose] public section

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ j ∈ range n, (f (2 * j) + f (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

end
end Finset
