/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D15

  `dataOk` of functions `1216` to `1296`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1216` to `1256` agree with the back end's.** -/
theorem dataOk_15a : (List.range' 1216 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1257` to `1296` agree with the back end's.** -/
theorem dataOk_15b : (List.range' 1257 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
