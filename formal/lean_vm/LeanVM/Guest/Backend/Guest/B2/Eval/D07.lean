/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D07

  `dataOk` of functions `568` to `648`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `568` to `608` agree with the back end's.** -/
theorem dataOk_07a : (List.range' 568 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `609` to `648` agree with the back end's.** -/
theorem dataOk_07b : (List.range' 609 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
