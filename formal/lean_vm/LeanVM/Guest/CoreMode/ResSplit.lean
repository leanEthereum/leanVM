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

/-! ## Hints -/

/-- Each entry of `l` passes `q` at its hint, the entries of `hs` in order (`0` past them). -/
def allH {α : Type} (q : Nat → α → Bool) : List Nat → List α → Bool
  | _, [] => true
  | [], a :: l => q 0 a && allH q [] l
  | h :: hs, a :: l => q h a && allH q hs l

theorem all_of_allH {α : Type} {p : α → Bool} {q : Nat → α → Bool} (hq : ∀ h a, q h a = true → p a = true) :
    ∀ (hs : List Nat) (l : List α), allH q hs l = true → l.all p = true
  | _, [], _ => rfl
  | [], a :: l, h => by
    simp only [allH, Bool.and_eq_true] at h
    simp [hq 0 a h.1, all_of_allH hq [] l h.2]
  | x :: hs, a :: l, h => by
    simp only [allH, Bool.and_eq_true] at h
    simp [hq x a h.1, all_of_allH hq hs l h.2]

/-- `sliceAll` with hints: `l`'s entries from `a` to `b` each pass `q` at its hint from `hs`. -/
def sliceAllH {α : Type} (q : Nat → α → Bool) (hs : List Nat) (l : List α) (a b : Nat) : Bool :=
  allH q hs ((l.drop a).take (b - a))

theorem sliceAll_of_H {α : Type} {p : α → Bool} {q : Nat → α → Bool} (hq : ∀ h a, q h a = true → p a = true)
    {hs : List Nat} {l : List α} {a b : Nat} (h : sliceAllH q hs l a b = true) : sliceAll p l a b = true :=
  all_of_allH hq hs _ h

end

end LeanVM.Guest.CoreMode
