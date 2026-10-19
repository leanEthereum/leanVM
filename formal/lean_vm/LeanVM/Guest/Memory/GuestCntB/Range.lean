/-
  LeanVM.Guest.Memory.GuestCntB.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntB.Data
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kwbhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kwbchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kwbhandJ.any (·.1 == j) ||
      ((kwblnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kwblookJ j) (kwbomLookJ j) false (kwbcertJ j) (kwbomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kwbStaticRange (a n : ℕ) : Prop := (List.range' a n).all kwbchkIdx = true

/-- **A function checked in ranges of its body**: its certificate a bound with no constants. -/
theorem kwbchkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kwbcertJ j = .stat pre b []) (hh : kwbhandJ.any (·.1 == j) = false)
    (hb : blockB (kwblookJ j) (kwbomLookJ j) false [] fn.params fn.name ([], []) fn.body = some R)
    (hl : (kwblnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kwbomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kwbchkIdx j = true := by
  unfold kwbchkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kwbStaticRange.get {a n j : ℕ} (h : kwbStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kwbchkIdx j = true := by
  unfold kwbStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
