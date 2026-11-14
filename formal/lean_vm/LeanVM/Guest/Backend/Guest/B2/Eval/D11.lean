/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D11

  `dataOk` of functions `892` to `972`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `892` to `932` agree with the back end's.** -/
theorem dataOk_11a : (List.range' 892 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `933` to `972` agree with the back end's.** -/
theorem dataOk_11b : (List.range' 933 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
