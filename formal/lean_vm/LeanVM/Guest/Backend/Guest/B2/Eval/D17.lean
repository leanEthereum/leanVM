/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D17

  `dataOk` of functions `1322` to `1397`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1322` to `1359` agree with the back end's.** -/
theorem dataOk_17a : (List.range' 1322 38).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1360` to `1397` agree with the back end's.** -/
theorem dataOk_17b : (List.range' 1360 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
