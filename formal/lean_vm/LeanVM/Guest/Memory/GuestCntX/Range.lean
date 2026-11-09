/-
  LeanVM.Guest.Memory.GuestCntX.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntX.Data
public import LeanVM.Guest.Memory.StaticSplit
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kwxhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kwxchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kwxhandJ.any (·.1 == j) ||
      ((kwxlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kwxlookJ j) (kwxomLookJ j) false (kwxcertJ j) (kwxomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kwxStaticRange (a n : ℕ) : Prop := (List.range' a n).all kwxchkIdx = true

/-- **A function checked in ranges of its body**, its certificate a bound. -/
theorem kwxchkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kwxcertJ j = .stat pre b ks) (hh : kwxhandJ.any (·.1 == j) = false)
    (hb : blockB (kwxlookJ j) (kwxomLookJ j) false ks fn.params fn.name ([], []) fn.body = some R)
    (hl : (kwxlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kwxomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kwxchkIdx j = true := by
  unfold kwxchkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kwxStaticRange.get {a n j : ℕ} (h : kwxStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kwxchkIdx j = true := by
  unfold kwxStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
