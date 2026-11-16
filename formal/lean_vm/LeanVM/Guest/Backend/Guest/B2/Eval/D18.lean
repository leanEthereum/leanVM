/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D18

  `dataOk` of functions `1398` to `1473`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1398` to `1435` agree with the back end's.** -/
theorem dataOk_18a : (List.range' 1398 38).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1436` to `1473` agree with the back end's.** -/
theorem dataOk_18b : (List.range' 1436 38).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
