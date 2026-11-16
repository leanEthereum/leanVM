/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D06

  `dataOk` of functions `469` to `546`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `469` to `507` agree with the back end's.** -/
theorem dataOk_06a : (List.range' 469 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `508` to `546` agree with the back end's.** -/
theorem dataOk_06b : (List.range' 508 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
