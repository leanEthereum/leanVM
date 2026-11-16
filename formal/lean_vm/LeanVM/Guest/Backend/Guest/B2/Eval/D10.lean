/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D10

  `dataOk` of functions `781` to `858`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `781` to `819` agree with the back end's.** -/
theorem dataOk_10a : (List.range' 781 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `820` to `858` agree with the back end's.** -/
theorem dataOk_10b : (List.range' 820 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
