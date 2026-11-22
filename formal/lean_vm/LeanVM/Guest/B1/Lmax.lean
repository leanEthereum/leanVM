/-
  LeanVM.Guest.B1.Lmax

  The largest of a list of naturals (`lmax`), which callees' bounds over their parameters' ranges are.
-/

module

public import Mathlib.Order.MinMax

namespace LeanVM.Guest.B1

@[expose] public section

/-- The largest of a list. -/
def lmax (l : List ℕ) : ℕ := l.foldl max 0

theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => ⟨le_rfl, fun _ h => by simp at h⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem le_lmax {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ lmax l := (foldl_max_ge l 0).2 x h

theorem le_lmax2 (f : ℕ → ℕ → ℕ) {A B a b : ℕ} (ha : a < A) (hb : b < B) :
    f a b ≤ lmax ((List.range A).flatMap fun a ↦ (List.range B).map (f a)) :=
  le_lmax (List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩)

end
end LeanVM.Guest.B1
