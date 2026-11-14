/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D12

  `dataOk` of functions `973` to `1053`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `973` to `1053` agree with the back end's.** -/
theorem dataOk_12 : (List.range' 973 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
