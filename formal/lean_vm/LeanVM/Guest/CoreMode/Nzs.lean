/-
  LeanVM.Guest.CoreMode.Nzs

  The parameters whose nonzero values the core route's certificates' residuals name.
-/

module

public import LeanVM.Guest.CoreMode.Assemble
public import LeanVM.Guest.CoreMode.Gen.FnData
public import LeanVM.Guest.EndExecW

/-!
# The core route's nonzero parameters

A routed function's certificate carries residuals only where its frame walk back-solves a product by
a divisor (`funC`'s residuals): each the nonzero value of a parameter listed here (`EndExec.NzOnly`), its function's
own, proved at every honest instance by it (`coreNzs_ok`).
-/

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

@[expose] public section

/-- The parameters whose nonzero values the core route's residuals are, by function: each function's own
(`FnReg.nzs`, `CoreMode/Fn/<f>/Data.lean`; nonzero by its `Sound.lean`, `coreNzs_ok` in `NzsOk.lean`). -/
abbrev coreNzs : List (String × V) := FnReg.nzs

end

end LeanVM.Guest.CoreMode
