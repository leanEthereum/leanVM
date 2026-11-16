/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D06

  `dataOk` of functions `487` to `567`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `487` to `527` agree with the back end's.** -/
theorem dataOk_06a : (List.range' 487 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `528` to `567` agree with the back end's.** -/
theorem dataOk_06b : (List.range' 528 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
