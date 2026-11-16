/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D09

  `dataOk` of functions `703` to `780`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `703` to `741` agree with the back end's.** -/
theorem dataOk_09a : (List.range' 703 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `742` to `780` agree with the back end's.** -/
theorem dataOk_09b : (List.range' 742 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
