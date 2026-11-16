/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D12

  `dataOk` of functions `937` to `1014`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `937` to `975` agree with the back end's.** -/
theorem dataOk_12a : (List.range' 937 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `976` to `1014` agree with the back end's.** -/
theorem dataOk_12b : (List.range' 976 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
