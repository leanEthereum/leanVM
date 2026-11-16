/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D19

  `dataOk` of functions `1474` to `1549`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1474` to `1511` agree with the back end's.** -/
theorem dataOk_19a : (List.range' 1474 38).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1512` to `1549` agree with the back end's.** -/
theorem dataOk_19b : (List.range' 1512 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
