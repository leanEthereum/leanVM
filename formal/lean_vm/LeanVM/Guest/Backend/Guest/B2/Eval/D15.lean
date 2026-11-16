/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D15

  `dataOk` of functions `1170` to `1245`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1170` to `1207` agree with the back end's.** -/
theorem dataOk_15a : (List.range' 1170 38).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1208` to `1245` agree with the back end's.** -/
theorem dataOk_15b : (List.range' 1208 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
