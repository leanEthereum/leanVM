/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D02

  `dataOk` of functions `163` to `243`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `163` to `243` agree with the back end's.** -/
theorem dataOk_02 : (List.range' 163 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
