/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D05

  `dataOk` of functions `391` to `468`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `391` to `429` agree with the back end's.** -/
theorem dataOk_05a : (List.range' 391 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `430` to `468` agree with the back end's.** -/
theorem dataOk_05b : (List.range' 430 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
