/-
  LeanVM.Guest.Budget.Chain

  The sum of a bound over a loop helper's iterations (`iterSum`).
-/

module

public import LeanVM.Guest.Budget.Kids

namespace LeanVM.Guest.Budget

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

/-- The sum of `B` over the `m` iterations from `c`. -/
def iterSum (B : ℕ → ℕ) (c m : ℕ) : ℕ := ((List.range m).map fun i => B (c + i)).sum

theorem iterSum_succ (B : ℕ → ℕ) (c m : ℕ) : iterSum B c (m + 1) = B c + iterSum B (c + 1) m := by
  unfold iterSum
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  congr 2
  congr 1
  funext i
  simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

end
end LeanVM.Guest.Budget
