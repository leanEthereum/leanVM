/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D13

  `dataOk` of functions `1054` to `1134`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1054` to `1094` agree with the back end's.** -/
theorem dataOk_13a : (List.range' 1054 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1095` to `1134` agree with the back end's.** -/
theorem dataOk_13b : (List.range' 1095 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
