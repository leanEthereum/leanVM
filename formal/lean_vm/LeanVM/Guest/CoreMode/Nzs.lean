/-
  LeanVM.Guest.CoreMode.Nzs

  The parameters whose nonzero values the core route's certificates' residuals name.
-/

module

public import LeanVM.Guest.CoreMode.Assemble
public import LeanVM.Guest.EndExecRM
public import LeanVM.Guest.CoreMode.Gen.MonoWalkOk
public import LeanVM.Guest.EndExecRVtG

/-!
# The core route's nonzero parameters

A routed function's certificate carries residuals only where its frame walk back-solves a product by
a divisor (`funC`'s residuals): each the nonzero value of a parameter listed here (`EndExec.NzOnly`),
proved at every honest instance by its family.
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

@[expose] public section

/-- The parameters whose nonzero values the core route's residuals are, by function. -/
def coreNzs : List (String × V) :=
  [("child_claim_list_mono_last__L0", .n 1), ("verify_tables", .n 133), ("verify_tables", .n 430)]

/-- Each listed parameter is nonzero at every honest instance of its function. -/
theorem coreNzs_ok : ∀ p ∈ coreNzs, NzVal p.1 p.2 := by
  intro p hp
  simp only [coreNzs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact nzVal_ml0 mono_ok
  · exact nzVal_vt133
  · exact nzVal_vt430

end

end LeanVM.Guest.CoreMode
