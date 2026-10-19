/-
  LeanVM.Guest.B2C.CplAll

  B2's completeness for every compiled function, from the completeness check alone.
-/

module

public import LeanVM.Guest.B2C.CplComp
public import LeanVM.Guest.Sound

/-!
# Every function's run

`cpl_run`'s other hypotheses hold of every function: the soundness windows' checks
(`End.winOk_of`, from the checked modules) and the power tree's (`End.certOf_pows_ok`).
-/

namespace LeanVM.Guest.B2C

open LeanVM.Guest

@[expose] public section

/-- **B2's completeness for function `j`**, given its completeness check. -/
theorem cplRun_of {j : ℕ} (h1 : 1 ≤ j) (hj : j < nFns) (hok : CplOk j) : CplRun j :=
  cpl_run h1 hj hok (End.winOk_of h1 hj) (End.certOf_pows_ok j)

end
end LeanVM.Guest.B2C
