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
  [28, 138, 225, 300, 359, 446, 521, 584, 631, 706, 769, 820, 855, 914, 961, 996]

/-- The template's number of the guest's value `j`: two more for each step without an address
constant below it. -/
def spRi (j : Nat) : Nat := j + 2 * spZeroR.countP (· < j)

/-- The template's numbering, on values. -/
def spUn (v : V) : V := ⟨v.path, v.tag, spRi v.idx⟩

/-- The values the guest's numbering leaves out, as a bit set: the two after each step without an address
constant (`spZero`). -/
def spGaps : Nat := spZero.foldl (fun b z ↦ b ||| 2 ^ (z + 1) ||| 2 ^ (z + 2)) 0

/-- `spUn` undoes `spRen` at `v`, as a Boolean (`spUnOK_iff`): `v` is not left out, one bit read. -/
def spUnOK (v : V) : Bool := !spGaps.testBit v.idx

private theorem spRi_spR_low :
    (List.range 1029).all (fun i ↦ spGaps.testBit i || spRi (spR i) == i) = true := by
  decide +kernel

theorem spRi_spR {i : Nat} (h : spGaps.testBit i = false) : spRi (spR i) = i := by
  by_cases hi : i < 1029
  · simpa [h] using List.all_eq_true.mp spRi_spR_low i (List.mem_range.mpr hi)
  have h1 : spZero.countP (· < i) = 16 := by
    refine (List.countP_eq_length.mpr fun z hz ↦ ?_).trans rfl
    simp only [spZero, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [decide_eq_true_eq]
    omega
  have hR : spR i = i - 32 := by rw [spR_eq, h1]
  have h2 : spZeroR.countP (· < spR i) = 16 := by
    refine (List.countP_eq_length.mpr fun z hz ↦ ?_).trans rfl
    simp only [spZeroR, List.mem_cons, List.not_mem_nil, or_false] at hz
    simp only [hR, decide_eq_true_eq]
    omega
  rw [spRi, h2, hR]
  omega

theorem spUnOK_iff {v : V} (h : spUnOK v = true) : spUn (spRen v) = v := by
  have e : spRi (spR v.idx) = v.idx := spRi_spR (by simpa [spUnOK] using h)
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
