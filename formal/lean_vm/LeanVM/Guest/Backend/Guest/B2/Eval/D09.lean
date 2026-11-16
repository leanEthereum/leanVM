/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D09

  `dataOk` of functions `730` to `810`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `730` to `770` agree with the back end's.** -/
theorem dataOk_09a : (List.range' 730 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `771` to `810` agree with the back end's.** -/
theorem dataOk_09b : (List.range' 771 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
