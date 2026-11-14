/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D17

  `dataOk` of functions `1378` to `1458`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1378` to `1418` agree with the back end's.** -/
theorem dataOk_17a : (List.range' 1378 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1419` to `1458` agree with the back end's.** -/
theorem dataOk_17b : (List.range' 1419 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
