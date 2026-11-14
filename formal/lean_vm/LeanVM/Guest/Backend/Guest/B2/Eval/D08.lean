/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D08

  `dataOk` of functions `649` to `729`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `649` to `729` agree with the back end's.** -/
theorem dataOk_08 : (List.range' 649 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
