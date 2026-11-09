/-
  LeanVM.Guest.Memory.GuestCntVD.Range

  Ranges of the guest's core IR whose static weight certificates the kernel checks.
-/

module

public import LeanVM.Guest.Memory.GuestCntVD.Data
public import LeanVM.Guest.Memory.StaticSplit
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

/-- The functions left to hand bounds, by index and name. -/
def kvdhandJ : List (ℕ × String) := []

/-- **The check of function `j`**: left to a hand bound, or its callees' indices name them and it
passes against its certificate. -/
noncomputable def kvdchkIdx (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => kvdhandJ.any (·.1 == j) ||
      ((kvdlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) &&
        chkFn (kvdlookJ j) (kvdomLookJ j) false (kvdcertJ j) (kvdomegaJ j) fn)

/-- The `n` functions from the `a`-th pass. -/
def kvdStaticRange (a n : ℕ) : Prop := (List.range' a n).all kvdchkIdx = true

/-- **A function checked in ranges of its body**, its certificate a bound. -/
theorem kvdchkIdx_of_split {j : ℕ} {fn : Fn} {pre : List (ℕ × ℕ)} {b : Aff} {ks : List (V × ℕ)} {R : Acc}
    (hfn : coreProgram[j]? = some fn) (hc : kvdcertJ j = .stat pre b ks) (hh : kvdhandJ.any (·.1 == j) = false)
    (hb : blockB (kvdlookJ j) (kvdomLookJ j) false ks fn.params fn.name ([], []) fn.body = some R)
    (hl : (kvdlnkJ j).all (fun q => decide ((coreProgram[q.2]?).map Fn.name = some q.1)) = true)
    (hle : (Aff.leB ⟨kvdomegaJ j + R.1.c, R.1.cs⟩ b && R.2.all (· ∈ pre)) = true) : kvdchkIdx j = true := by
  unfold kvdchkIdx
  rw [hfn]
  simp only [hh, hl, Bool.true_and, Bool.false_or]
  unfold chkFn
  rw [hc]
  simp only
  rw [blockR_eq, hb]
  exact hle

theorem kvdStaticRange.get {a n j : ℕ} (h : kvdStaticRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    kvdchkIdx j = true := by
  unfold kvdStaticRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
