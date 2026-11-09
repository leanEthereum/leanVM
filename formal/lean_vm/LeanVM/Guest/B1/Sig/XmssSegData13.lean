/-
  LeanVM.Guest.B1.Sig.XmssSegData13

  `__loop2`'s body agrees with the template `xSeg` on segment statement 82 (a dispatch).
-/

module

public import LeanVM.Guest.Data.Core17
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.Decide

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

open scoped Dec in
theorem xSeg_slice_82 : ((Data.core36.body.drop 9).drop 82).take 1 = ((xSeg ++ l2Post).drop 82).take 1 := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
