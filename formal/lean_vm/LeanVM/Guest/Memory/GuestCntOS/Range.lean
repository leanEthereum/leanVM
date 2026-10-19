/-
  LeanVM.Guest.Memory.GuestCntOS.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntOS.Data
public import LeanVM.Guest.Memory.StaticSound
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kwoshandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kwoschkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kwoshandJ.any (·.1 == j) ||
      ((kwoslnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kwoslookJ j) (kwosomLookJ j) false (kwoscertJ j) (kwosomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kwosStaticRange (a n : ℕ) : Prop := (List.range' a n).all kwoschkIdx = true

/-- **A function checked in ranges of its body**: its certificate a bound with no constants. -/
theorem kwoschkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kwoscertJ j = .stat pre b []) (hh : kwoshandJ.any (·.1 == j) = false)
    (hb : blockB (kwoslookJ j) (kwosomLookJ j) false [] fn.params fn.name ([], []) fn.body = some R)
    (hl : (kwoslnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kwosomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kwoschkIdx j = true := by
  unfold kwoschkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kwosStaticRange.get {a n j : ℕ} (h : kwosStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kwoschkIdx j = true := by
  unfold kwosStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
