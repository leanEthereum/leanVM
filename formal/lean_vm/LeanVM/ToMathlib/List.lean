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
  simp [List.getD_eq_getElem?_getD, h]

/-- A running maximum bounds its start and every element. -/
theorem foldl_max_ge : ∀ (l : List ℕ) (a : ℕ), a ≤ l.foldl max a ∧ ∀ x ∈ l, x ≤ l.foldl max a
  | [], _ => ⟨le_rfl, fun _ h => by simp at h⟩
  | y :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_max_ge l (max a y)
    refine ⟨le_trans (le_max_left a y) h1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_trans (le_max_right a x) h1
    · exact h2 x hx

theorem headD_eq_getD {α : Type*} (l : List α) (d : α) : l.headD d = l.getD 0 d := by
  cases l <;> rfl

end
end List
