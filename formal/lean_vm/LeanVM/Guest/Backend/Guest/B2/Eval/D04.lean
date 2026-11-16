/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D04

  `dataOk` of functions `313` to `390`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `313` to `351` agree with the back end's.** -/
theorem dataOk_04a : (List.range' 313 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `352` to `390` agree with the back end's.** -/
theorem dataOk_04b : (List.range' 352 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
