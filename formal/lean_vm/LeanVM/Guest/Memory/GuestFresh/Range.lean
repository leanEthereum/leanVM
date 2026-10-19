/-
  LeanVM.Guest.Memory.GuestFresh.Range

  Ranges of the guest's core IR whose range-check temporaries the kernel checks fresh, and their
  concatenation.
-/

module

public import LeanVM.Guest.Memory.Fresh
public import LeanVM.Guest.CoreData

namespace LeanVM.Guest

open Core Memory

@[expose] public section

/-- The `n` functions of `coreProgram` from its `a`-th have fresh temporaries. -/
def FreshRange (a n : ℕ) : Prop :=
  ((coreProgram.drop a).take n).all (fun fn => fn.freshB) = true

/-- Two adjacent ranges are one. -/
theorem FreshRange.append' {a n m b k : ℕ} (h : FreshRange a n) (h' : FreshRange b m)
    (hb : a + n = b) (hk : n + m = k) : FreshRange a k := by
  subst hb hk
  unfold FreshRange at *
  rw [List.take_add, List.all_append, List.drop_drop, Bool.and_eq_true]
  exact ⟨h, h'⟩

/-- Every function of a range has fresh temporaries. -/
theorem FreshRange.fresh {a n : ℕ} (h : FreshRange a n) {fn : Fn}
    (hfn : fn ∈ (coreProgram.drop a).take n) : fn.Fresh := by
  unfold FreshRange at h
  rw [List.all_eq_true] at h
  exact fn_fresh_of_freshB (h fn hfn)

end
end LeanVM.Guest
