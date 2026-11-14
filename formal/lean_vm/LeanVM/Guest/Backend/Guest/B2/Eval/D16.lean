/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D16

  `dataOk` of functions `1297` to `1377`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1297` to `1377` agree with the back end's.** -/
theorem dataOk_16 : (List.range' 1297 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
