/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D01

  `dataOk` of functions `82` to `162`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `82` to `122` agree with the back end's.** -/
theorem dataOk_01a : (List.range' 82 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `123` to `162` agree with the back end's.** -/
theorem dataOk_01b : (List.range' 123 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
