/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D12

  `dataOk` of functions `973` to `1053`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `973` to `1013` agree with the back end's.** -/
theorem dataOk_12a : (List.range' 973 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1014` to `1053` agree with the back end's.** -/
theorem dataOk_12b : (List.range' 1014 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
