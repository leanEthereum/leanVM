/-
  LeanVM.Guest.CoreMode.NzsOk

  The core route's nonzero parameters (`coreNzs`) nonzero at every honest instance of their functions.
-/

module

public import LeanVM.Guest.CoreMode.Nzs
public import LeanVM.Guest.CoreMode.Gen.FnSound

namespace LeanVM.Guest.CoreMode

open LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.EndExec

public section

/-- Each listed parameter is nonzero at every honest instance of its function (each function's own, `FnReg.nzs_ok`). -/
theorem coreNzs_ok : ∀ p ∈ coreNzs, NzVal p.1 p.2 := FnReg.nzs_ok

end

end LeanVM.Guest.CoreMode
