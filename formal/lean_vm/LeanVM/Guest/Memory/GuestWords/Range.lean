/-
  LeanVM.Guest.Memory.GuestWords.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestWords.Data
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def whandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def wchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => whandJ.any (·.1 == j) ||
      ((wlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (wlookJ j) (womLookJ j) true (wcertJ j) (womegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def wStaticRange (a n : ℕ) : Prop := (List.range' a n).all wchkIdx = true

/-- **A function checked in ranges of its body**: its certificate a bound with no constants. -/
theorem wchkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : wcertJ j = .stat pre b []) (hh : whandJ.any (·.1 == j) = false)
    (hb : blockB (wlookJ j) (womLookJ j) true [] fn.params fn.name ([], []) fn.body = some R)
    (hl : (wlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨womegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : wchkIdx j = true := by
  unfold wchkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem wStaticRange.get {a n j : ℕ} (h : wStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    wchkIdx j = true := by
  unfold wStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
