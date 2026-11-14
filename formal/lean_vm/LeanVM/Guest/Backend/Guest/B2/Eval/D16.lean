/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D16

  `dataOk` of functions `1297` to `1377`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1297` to `1337` agree with the back end's.** -/
theorem dataOk_16a : (List.range' 1297 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1338` to `1377` agree with the back end's.** -/
theorem dataOk_16b : (List.range' 1338 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
