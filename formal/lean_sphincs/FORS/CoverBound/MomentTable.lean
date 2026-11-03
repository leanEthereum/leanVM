import FORS.CoverBound.MomentBounds

/-! **The per-tree moment tables.** Upper bounds of `Ψ1(n)` and `Ψ2(n)` for `n ≤ 150`, as the lists
of their numerators over `2^128` (`P1L`, `P2L`, which `Certificates/Build.lean` reads) and the
rationals they stand for (`P1tab`, `P2tab`). The kernel computes them from the closed forms of
`CoverBound/MomentBounds`; nothing is tabulated. -/

namespace FORS.Security.H0

set_option linter.unusedSectionVars false

/-- The numerators over `2^128` of the upper bounds of `Ψ1(n)`, `n ≤ 150`. -/
def P1L (a : ℕ) : List ℕ := (List.range 151).map (p1N a)

/-- Upper bounds of `Ψ1(n)`, `n ≤ 150`. -/
def P1tab (a : ℕ) : List ℚ := (P1L a).map fun x : ℕ => (x : ℚ) / 2 ^ 128

theorem P1L_eq (a : ℕ) : (P1L a).map (fun x : ℕ => (x : ℚ) / 2 ^ 128) = P1tab a := rfl

theorem length_P1L (a : ℕ) : (P1L a).length = 151 := by
  rw [P1L, List.length_map, List.length_range]

/-- The numerators over `2^128` of the upper bounds of `Ψ2(n)`, `n ≤ 150`. -/
def P2L (a : ℕ) : List ℕ := (List.range 151).map (p2N a)

/-- Upper bounds of `Ψ2(n)`, `n ≤ 150`. -/
def P2tab (a : ℕ) : List ℚ := (P2L a).map fun x : ℕ => (x : ℚ) / 2 ^ 128

theorem P2L_eq (a : ℕ) : (P2L a).map (fun x : ℕ => (x : ℚ) / 2 ^ 128) = P2tab a := rfl

theorem length_P2L (a : ℕ) : (P2L a).length = 151 := by
  rw [P2L, List.length_map, List.length_range]

theorem getD_P1tab (a n : ℕ) (hn : n ≤ 150) : (P1tab a).getD n 0 = P1Q a n := by
  rw [P1tab, P1L, List.map_map, getD_map_range _ _ _ _ (by omega)]
  rfl

theorem getD_P2tab (a n : ℕ) (hn : n ≤ 150) : (P2tab a).getD n 0 = P2Q a n := by
  rw [P2tab, P2L, List.map_map, getD_map_range _ _ _ _ (by omega)]
  rfl

variable [Params]

open Concrete

theorem Ψ1R_le_tab (n : ℕ) (hn : n ≤ 150) : Ψ1R n ≤ (((P1tab forsHeight).getD n 0 : ℚ) : ℝ) := by
  rw [getD_P1tab forsHeight n hn]
  exact Ψ1R_le n

theorem Ψ2R_le_tab (n : ℕ) (hn : n ≤ 150) : Ψ2R n ≤ (((P2tab forsHeight).getD n 0 : ℚ) : ℝ) := by
  rw [getD_P2tab forsHeight n hn]
  exact Ψ2R_le n

end FORS.Security.H0
