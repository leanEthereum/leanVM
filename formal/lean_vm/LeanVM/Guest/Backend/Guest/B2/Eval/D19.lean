/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D19

  `dataOk` of functions `1540` to `1601`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1540` to `1570` agree with the back end's.** -/
theorem dataOk_19a : (List.range' 1540 31).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1571` to `1601` agree with the back end's.** -/
theorem dataOk_19b : (List.range' 1571 31).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
