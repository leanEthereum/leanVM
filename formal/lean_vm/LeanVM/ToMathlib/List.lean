/-
  LeanVM.ToMathlib.List

  List lemmas the proofs share that Mathlib does not state.
-/

module

public import Mathlib.Data.List.GetD
public import Mathlib.Order.MinMax

/-!
# Lists

Generic facts about `List`, one home for each: an entry of `(List.range n).map f`, and the bounds
of a running maximum. They are in Mathlib's namespace and naming, as candidates for upstreaming.
-/

namespace List

@[expose] public section

theorem getD_map_range {α : Type*} (f : ℕ → α) {n c : ℕ} (h : c < n) (d : α) :
    ((List.range n).map f).getD c d = f c := by
  simp [h]

/-- A running maximum bounds its start and every element. -/
theorem foldl_max_ge {α : Type*} [LinearOrder α] :
    ∀ (l : List α) (a : α), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => by simp
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    exact ⟨(le_max_left a y).trans h1, forall_mem_cons.mpr ⟨(le_max_right a y).trans h1, h2⟩⟩

end
end List
