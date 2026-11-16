/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D08

  `dataOk` of functions `625` to `702`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `625` to `663` agree with the back end's.** -/
theorem dataOk_08a : (List.range' 625 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `664` to `702` agree with the back end's.** -/
theorem dataOk_08b : (List.range' 664 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
