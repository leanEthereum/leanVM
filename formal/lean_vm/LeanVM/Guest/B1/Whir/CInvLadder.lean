/-
  LeanVM.Guest.B1.Whir.CInvLadder

  The candidates' ladders' static facts the backwards run needs, decided by the kernel.
-/

module

public import Statement.LeanVmVerifier

/-!
# The ladders' rates and queries

`ladderRunOk μ r`: every level of `Whir.ladder μ r` has a rate exponent in `[1, 128 - μ]` and some
queries; `ladderRunOk_all`: at every stack size `μ ∈ [20, 30]`, `r ∈ [1, 4]` (a kernel check).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters

@[expose] public section

/-- Every level of the ladder has a rate exponent in `[1, 128 - μ]` and some queries. -/
def ladderRunOk (μ r : ℕ) : Bool :=
  match Whir.ladder μ r with
  | some cfg => cfg.all fun l ↦ decide (1 ≤ l.logInvRate) && decide (μ + l.logInvRate ≤ 128) &&
      decide (0 < l.queries)
  | none => true

/-- **At every candidate.** -/
theorem ladderRunOk_all : ((List.range 11).all fun i ↦ (List.range 4).all fun j ↦
    ladderRunOk (20 + i) (1 + j)) = true := by
  decide +kernel

theorem ladderRunOk_at {μ r : ℕ} (h1 : 20 ≤ μ) (h2 : μ ≤ 30) (h3 : 1 ≤ r) (h4 : r ≤ 4) :
    ladderRunOk μ r = true := by
  have h := List.all_eq_true.mp ladderRunOk_all (μ - 20) (List.mem_range.mpr (by omega))
  have h' := List.all_eq_true.mp h (r - 1) (List.mem_range.mpr (by omega))
  rwa [show 20 + (μ - 20) = μ by omega, show 1 + (r - 1) = r by omega] at h'

end
end LeanVM.Guest.B1.Whir
