/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D04

  `dataOk` of functions `325` to `405`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `325` to `365` agree with the back end's.** -/
theorem dataOk_04a : (List.range' 325 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `366` to `405` agree with the back end's.** -/
theorem dataOk_04b : (List.range' 366 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
