/-
  LeanVM.Guest.Backend.Sound.Obl.Steps

  A test of every item of a list from the tests of its consecutive runs: what `Eval/All.lean`
  assembles the evaluations of `Eval/` with.
-/

module

namespace LeanVM.Guest.Backend.Obl

@[expose] public section

theorem range_step {p : Nat → Bool} {a n b m k : Nat} (h1 : (List.range' a n).all p = true)
    (hb : a + n = b) (h2 : (List.range' b m).all p = true) (hk : n + m = k) :
    (List.range' a k).all p = true := by
  subst hb hk
  rw [← List.range'_append_1, List.all_append, h1, h2]
  rfl

theorem all_step {α : Type} {l : List α} {p : α → Bool} {a n b : Nat}
    (h1 : ((l.drop a).take n).all p = true) (hb : a + n = b) (h2 : (l.drop b).all p = true) :
    (l.drop a).all p = true := by
  have e : (l.drop a).drop n = l.drop b := by rw [List.drop_drop, ← hb, Nat.add_comm]
  rw [← List.take_append_drop n (l.drop a), List.all_append, h1, e, h2]
  rfl

theorem all_end {α : Type} {l : List α} {p : α → Bool} {a : Nat} (h : l.length ≤ a) :
    (l.drop a).all p = true := by
  rw [List.drop_eq_nil_of_le h]
  rfl

end
end LeanVM.Guest.Backend.Obl
