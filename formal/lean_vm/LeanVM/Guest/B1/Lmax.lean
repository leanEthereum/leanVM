/-
  LeanVM.Guest.B1.Lmax

  The largest of a list of naturals (`lmax`), which callees' bounds over their parameters' ranges are.
-/

module

public import Mathlib.Order.MinMax
public import LeanVM.ToMathlib.List

namespace LeanVM.Guest.B1

@[expose] public section

/-- The largest of a list. -/
def lmax (l : List ℕ) : ℕ := l.foldl max 0

theorem le_lmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ lmax l := (List.foldl_max_ge l 0).2 x h

theorem le_lmax2 (f : ℕ → ℕ → ℕ) {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    f a b ≤ lmax ((List.range A).flatMap fun a ↦ (List.range B).map (f a)) :=
  le_lmax (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)

end
end LeanVM.Guest.B1
