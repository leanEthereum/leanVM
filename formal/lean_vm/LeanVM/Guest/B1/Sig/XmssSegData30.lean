/-
  LeanVM.Guest.B1.Sig.XmssSegData30

  `__loop2`'s body agrees with the template `xSeg` on segment statement 225 (a dispatch).
-/

module

public import LeanVM.Guest.Data.Core17
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xSeg_slice_225 : ((Data.core36.body.drop 9).drop 225).take 1 = ((xSeg ++ l2Post).drop 225).take 1 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
