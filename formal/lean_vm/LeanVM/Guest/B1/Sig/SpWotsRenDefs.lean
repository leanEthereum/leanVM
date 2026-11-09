/-
  LeanVM.Guest.B1.Sig.SpWotsRenDefs

  The template's numbering of `sp_wots`'s values, undoing the guest's (`spRen`).
-/

module

public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Sig.Frame

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- The guest's numbers of the steps without an address constant (`spZero`, renumbered). -/
def spZeroR : List Nat :=
  [29, 146, 241, 324, 391, 486, 569, 640, 695, 778, 849, 908, 951, 1018, 1073, 1116]

/-- The template's number of the guest's value `j`: two more for each step without an address
constant below it. -/
def spRi (j : Nat) : Nat := j + 2 * spZeroR.countP (· < j)

/-- The template's numbering, on values. -/
def spUn (v : V) : V := ⟨v.path, v.tag, spRi v.idx⟩

/-- `spUn` undoes `spRen` at `v`, as a Boolean (`spUnOK_iff`). -/
def spUnOK (v : V) : Bool := Nat.beq (spRi (spR v.idx)) v.idx

theorem spUnOK_iff {v : V} (h : spUnOK v = true) : spUn (spRen v) = v := by
  have e : spRi (spR v.idx) = v.idx := Nat.eq_of_beq_eq_true h
  cases v
  simp only [spUn, spRen] at e ⊢
  rw [e]

theorem vals_drop_step {l : List Stmt} {a n : Nat} {P : V → Bool}
    (h1 : (Stmt.valsList ((l.drop a).take n)).all P = true)
    (h2 : ∀ v ∈ Stmt.valsList (l.drop (a + n)), P v = true) :
    ∀ v ∈ Stmt.valsList (l.drop a), P v = true := by
  intro v hv
  rw [← List.take_append_drop n (l.drop a), valsList_append, List.drop_drop] at hv
  rcases List.mem_append.mp hv with h | h
  · exact List.all_eq_true.mp h1 v h
  · exact h2 v h

end
end LeanVM.Guest.B1.Sig
