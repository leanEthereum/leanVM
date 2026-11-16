/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D01

  `dataOk` of functions `79` to `156`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `79` to `117` agree with the back end's.** -/
theorem dataOk_01a : (List.range' 79 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `118` to `156` agree with the back end's.** -/
theorem dataOk_01b : (List.range' 118 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
