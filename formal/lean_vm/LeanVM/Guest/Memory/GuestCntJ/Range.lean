/-
  LeanVM.Guest.Memory.GuestCntJ.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntJ.Data
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kwjhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kwjchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kwjhandJ.any (·.1 == j) ||
      ((kwjlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kwjlookJ j) (kwjomLookJ j) false (kwjcertJ j) (kwjomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kwjStaticRange (a n : ℕ) : Prop := (List.range' a n).all kwjchkIdx = true

/-- **A function checked in ranges of its body**: its certificate a bound with no constants. -/
theorem kwjchkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kwjcertJ j = .stat pre b []) (hh : kwjhandJ.any (·.1 == j) = false)
    (hb : blockB (kwjlookJ j) (kwjomLookJ j) false [] fn.params fn.name ([], []) fn.body = some R)
    (hl : (kwjlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kwjomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kwjchkIdx j = true := by
  unfold kwjchkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kwjStaticRange.get {a n j : ℕ} (h : kwjStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kwjchkIdx j = true := by
  unfold kwjStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
