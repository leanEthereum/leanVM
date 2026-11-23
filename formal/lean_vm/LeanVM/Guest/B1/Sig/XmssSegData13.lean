/-
  LeanVM.Guest.B1.Sig.XmssSegData13

  `main_loop2`'s body agrees with the template `xSeg` on one segment statement (a dispatch).
-/

module

public import LeanVM.Guest.Pack.main_loop2.Core
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«main_loop2»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem xSeg_slice_82 : (((Fn.«main_loop2».core).body.drop (pos% «main_loop2» "s3.i3:verify_lean_xmss.s0#0")).drop (span% «main_loop2» "pp" "value@9217")).take 1 = ((xSeg ++
    l2Post).drop
    82).take 1 :=
  stmtsEqb_sound (by decide +kernel)

end
end LeanVM.Guest.B1.Sig
