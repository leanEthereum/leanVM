/-
  LeanVM.Guest.Backend.Guest.B2.Eval.D10

  `dataOk` of functions `811` to `891`, decided by the kernel.
-/

module

public import LeanVM.Guest.Backend.Guest.B2.Data

namespace LeanVM.Guest.Backend.B2

@[expose] public section

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `811` to `851` agree with the back end's.** -/
theorem dataOk_10a : (List.range' 811 41).all dataOk = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- **The certificate data of functions `852` to `891` agree with the back end's.** -/
theorem dataOk_10b : (List.range' 852 40).all dataOk = true := by decide +kernel

end
end LeanVM.Guest.Backend.B2
