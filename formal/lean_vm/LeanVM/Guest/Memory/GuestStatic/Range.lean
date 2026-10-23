/-
  LeanVM.Guest.Memory.GuestStatic.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestStatic.Data
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def handJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def chkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => handJ.any (·.1 == j) ||
      ((lnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (lookJ j) (omLookJ j) false (certJ j) (omegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def StaticRange (a n : ℕ) : Prop := (List.range' a n).all chkIdx = true

/-- **A function checked in ranges of its body**: its certificate a bound with no constants. -/
theorem chkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : certJ j = .stat pre b []) (hh : handJ.any (·.1 == j) = false)
    (hb : blockB (lookJ j) (omLookJ j) false [] fn.params fn.name ([], []) fn.body = some R)
    (hl : (lnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨omegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : chkIdx j = true := by
  unfold chkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem StaticRange.get {a n j : ℕ} (h : StaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    chkIdx j = true := by
  unfold StaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
