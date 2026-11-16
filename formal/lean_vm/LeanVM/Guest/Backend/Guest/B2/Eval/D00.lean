/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D00

  `dataOk` of functions `1` to `78`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `1` to `39` agree with the back end's.** -/
theorem dataOk_00a : (List.range' 1 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `40` to `78` agree with the back end's.** -/
theorem dataOk_00b : (List.range' 40 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
