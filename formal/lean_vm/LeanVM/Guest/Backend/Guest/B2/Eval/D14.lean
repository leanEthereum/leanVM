/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D14

  `dataOk` of functions `1093` to `1169`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1093` to `1131` agree with the back end's.** -/
theorem dataOk_14a : (List.range' 1093 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1132` to `1169` agree with the back end's.** -/
theorem dataOk_14b : (List.range' 1132 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
