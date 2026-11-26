/-
  LeanVM.Guest.B1.Sig.XmssSegData

  `main_loop2` (`Fn.«main_loop2».core`) in the guest's core IR is `l2Pre`, the leanXMSS check
  `xSeg`, then `l2Post`.
-/

module

public import LeanVM.Guest.Pack.main_loop2.Core
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.KernelLit

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`main_loop2`'s body**: the check `xSeg` between `l2Pre` and `l2Post` (`kernel_rfl`). -/
kernel_rfl loop2_split : (Fn.«main_loop2».core).body = l2Pre ++ (xSeg ++ l2Post)

end
end LeanVM.Guest.B1.Sig
