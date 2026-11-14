/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D00

  `dataOk` of functions `1` to `81`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1` to `81` agree with the back end's.** -/
theorem dataOk_00 : (List.range' 1 81).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
