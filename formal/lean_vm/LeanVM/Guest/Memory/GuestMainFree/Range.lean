/-
  LeanVM.Guest.Memory.GuestMainFree.Range

  Ranges of the guest's core IR none of whose functions calls `main`.
-/

module

public import LeanVM.Guest.Memory.SizeTotal
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- No callee of function `j` is `main`. -/
noncomputable def mainFreeJ (j : ℕ) : Bool :=
  match coreProgram[j]? with
  | none => true
  | some fn => (Stmt.blockCallees fn.body).all fun g => decide (g ≠ "main")

/-- The `n` functions from the `a`-th call no `main`. -/
def MainFreeRange (a n : ℕ) : Prop := (List.range' a n).all mainFreeJ = true

theorem MainFreeRange.get {a n j : ℕ} (h : MainFreeRange a n) (h1 : a ≤ j) (h2 : j < a + n) :
    mainFreeJ j = true := by
  unfold MainFreeRange at h
  rw [List.all_eq_true] at h
  exact h j (List.mem_range'_1.mpr ⟨h1, h2⟩)

end
end LeanVM.Guest
