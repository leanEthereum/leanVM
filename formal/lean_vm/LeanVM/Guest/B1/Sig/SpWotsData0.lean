/-
  LeanVM.Guest.B1.Sig.SpWotsData0

  `sp_wots` in the guest's core IR agrees with the template `spBody` on the copies, the powers and digit groups 0 to 10.
-/

module

public import LeanVM.Guest.Pack.sp_wots.Core
public import LeanVM.Guest.B1.Sig.SpWotsLayout
public import LeanVM.Guest.B1.Common.Basic
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«sp_wots»

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-! The copies, the powers and digit groups 0 to 10,
compared by `stmtsEqb` in runs, each its own kernel evaluation to bound its memory. -/

set_option maxRecDepth 100000 in
theorem spBody_run_0 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s0#0")).take (pos% «sp_wots» "powers[6]")) ((spBody.drop 0).take (pos% «sp_wots» "powers[6]")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_8 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s2#0[6]")).take (span% «sp_wots» "powers[6]" "digit_product@1~1[1]")) ((spBody.drop (pos% «sp_wots» "powers[6]")).take (span% «sp_wots» "powers[6]" "digit_product@1~1[1]")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_16 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u0.s2#1[1]")).take (span% «sp_wots» "digit_product@1~1[1]" "s6.u1.s1#1")) ((spBody.drop (pos% «sp_wots» "digit_product@1~1[1]")).take (span% «sp_wots» "digit_product@1~1[1]" "s6.u1.s1#1")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_24 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u1.s1#1")).take (span% «sp_wots» "s6.u1.s1#1" "group@4")) ((spBody.drop (pos% «sp_wots» "s6.u1.s1#1")).take (span% «sp_wots» "s6.u1.s1#1" "group@4")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_32 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u3.s0#0")).take (span% «sp_wots» "group@4" "digit_product@5~1")) ((spBody.drop (pos% «sp_wots» "group@4")).take (span% «sp_wots» "group@4" "digit_product@5~1")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_40 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u4.s2#1")).take (span% «sp_wots» "digit_product@5~1" "s6.u6.s1#0")) ((spBody.drop (pos% «sp_wots» "digit_product@5~1")).take (span% «sp_wots» "digit_product@5~1" "s6.u6.s1#0")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_48 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u6.s1#0")).take (span% «sp_wots» "s6.u6.s1#0" "value@1009")) ((spBody.drop (pos% «sp_wots» "s6.u6.s1#0")).take (span% «sp_wots» "s6.u6.s1#0" "value@1009")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_56 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u7.s2.a0.i0:walk_group.s0.u0.s0.i0:walk.s1.e.s0#0")).take (span% «sp_wots» "value@1009" "s6.u9.s1#1")) ((spBody.drop (pos% «sp_wots» "value@1009")).take (span% «sp_wots» "value@1009" "s6.u9.s1#1")) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem spBody_run_64 :
    stmtsEqb (((Fn.«sp_wots».core).body.drop (pos% «sp_wots» "s6.u9.s1#1")).take (span% «sp_wots» "s6.u9.s1#1" "group@12")) ((spBody.drop (pos% «sp_wots» "s6.u9.s1#1")).take (span% «sp_wots» "s6.u9.s1#1" "group@12")) = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Sig
