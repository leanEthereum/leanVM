/-
  LeanVM.Guest.B1.Sig.XmssSegData30

  `main_loop2`'s body agrees with the template `xSeg` on segment statement 225 (a dispatch).
-/

module

public import LeanVM.Guest.Data.Names
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem xSeg_slice_225 : (((fn% «main_loop2»).body.drop 9).drop 225).take 1 = ((xSeg ++
    l2Post).drop 225).take 1 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
