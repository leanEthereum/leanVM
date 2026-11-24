/-
  LeanVM.Guest.CoreMode.ResSplit

  A list check in slices, each its own kernel evaluation: for a function whose heap certificate has more residuals
  than `core.py`'s `RES_B`, its `resOk` (the kernel's memory goes by declaration).
-/

module

namespace LeanVM.Guest.CoreMode

@[expose] public section

/-- `l`'s entries from `a` to `b` all satisfy `p`. -/
def sliceAll {α : Type} (p : α → Bool) (l : List α) (a b : Nat) : Bool := ((l.drop a).take (b - a)).all p

theorem all_drop_of_slice {α : Type} {p : α → Bool} {l : List α} {a b : Nat} (hab : a ≤ b)
    (h : sliceAll p l a b = true) (hr : (l.drop b).all p = true) : (l.drop a).all p = true := by
  have e : (l.drop a).drop (b - a) = l.drop b := by rw [List.drop_drop]; congr 1; omega
  rw [← List.take_append_drop (b - a) (l.drop a), List.all_append, e]
  exact Bool.and_eq_true_iff.2 ⟨h, hr⟩

theorem all_drop_of_le {α : Type} {p : α → Bool} {l : List α} {n : Nat} (h : l.length ≤ n) :
    (l.drop n).all p = true := by
  rw [List.drop_eq_nil_of_le h, List.all_nil]

theorem all_of_drop_zero {α : Type} {p : α → Bool} {l : List α} (h : (l.drop 0).all p = true) : l.all p = true :=
  by rwa [List.drop_zero] at h

end

end LeanVM.Guest.CoreMode
