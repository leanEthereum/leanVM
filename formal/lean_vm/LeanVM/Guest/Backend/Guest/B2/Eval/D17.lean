/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D17

  `dataOk` of functions `1378` to `1458`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1378` to `1458` agree with the back end's.** -/
theorem dataOk_17 : (List.range' 1378 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
