/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D02

  `dataOk` of functions `157` to `234`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `157` to `195` agree with the back end's.** -/
theorem dataOk_02a : (List.range' 157 39).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `196` to `234` agree with the back end's.** -/
theorem dataOk_02b : (List.range' 196 39).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
