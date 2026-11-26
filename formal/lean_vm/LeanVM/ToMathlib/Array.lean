/-
  LeanVM.ToMathlib.Array

  General `Array` lemmas Mathlib does not state, in Mathlib's namespace and naming.
-/

module

namespace Array

public section

universe u

theorem getD_ofFn {α : Type u} {n : Nat} (f : Fin n → α) {i : Nat} (h : i < n) (d : α) :
    (ofFn f).getD i d = f ⟨i, h⟩ := by
  simp [Array.getD_eq_getD_getElem?, h]

end

end Array
