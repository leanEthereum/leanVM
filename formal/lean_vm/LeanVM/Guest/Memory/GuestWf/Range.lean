/-
  LeanVM.Guest.Memory.GuestWf.Range

  Ranges of the guest's core IR whose well-formedness the kernel checks, and their concatenation.
-/

module

public import LeanVM.Guest.Memory.Tree
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- The `n` functions of `coreProgram` from its `a`-th are well formed. -/
def WfRange (a n : ℕ) : Prop :=
  ((coreProgram.drop a).take n).all (fun fn => Stmt.wfList coreProgram fn.body) = true

/-- Two adjacent ranges are one. -/
theorem WfRange.append {a n m : ℕ} (h : WfRange a n) (h' : WfRange (a + n) m) :
    WfRange a (n + m) := by
  unfold WfRange at *
  rw [List.take_add, List.all_append, List.drop_drop, Bool.and_eq_true]
  exact ⟨h, h'⟩

/-- The same, with the sums as literals. -/
theorem WfRange.append' {a n m b k : ℕ} (h : WfRange a n) (h' : WfRange b m) (hb : a + n = b) (hk : n + m = k) :
    WfRange a k := by
  subst hb hk
  exact h.append h'

end
end LeanVM.Guest
