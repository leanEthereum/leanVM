/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D16

  `dataOk` of functions `1246` to `1321`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1246` to `1283` agree with the back end's.** -/
theorem dataOk_16a : (List.range' 1246 38).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1284` to `1321` agree with the back end's.** -/
theorem dataOk_16b : (List.range' 1284 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
