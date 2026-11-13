/-
  LeanVM.Guest.B1.Sig.XmssSegData

  `main_loop2` (`Fn.«main_loop2».core`) in the guest's core IR is `l2Pre`, the leanXMSS check
  `xSeg`, then `l2Post`.
-/

module

public import LeanVM.Guest.Pack.main_loop2.Core
public import LeanVM.Guest.B1.Sig.XmssSegT
import LeanVM.Guest.B1.Sig.Decide
import LeanVM.Guest.B1.Sig.XmssSegData1
import LeanVM.Guest.B1.Sig.XmssSegData2
import LeanVM.Guest.B1.Sig.XmssSegData3
import LeanVM.Guest.B1.Sig.XmssSegData4
import LeanVM.Guest.B1.Sig.XmssSegData5
import LeanVM.Guest.B1.Sig.XmssSegData6
import LeanVM.Guest.B1.Sig.XmssSegData7
import LeanVM.Guest.B1.Sig.XmssSegData8
import LeanVM.Guest.B1.Sig.XmssSegData9
import LeanVM.Guest.B1.Sig.XmssSegData10
import LeanVM.Guest.B1.Sig.XmssSegData11
import LeanVM.Guest.B1.Sig.XmssSegData12
import LeanVM.Guest.B1.Sig.XmssSegData13
import LeanVM.Guest.B1.Sig.XmssSegData14
import LeanVM.Guest.B1.Sig.XmssSegData15
import LeanVM.Guest.B1.Sig.XmssSegData16
import LeanVM.Guest.B1.Sig.XmssSegData17
import LeanVM.Guest.B1.Sig.XmssSegData18
import LeanVM.Guest.B1.Sig.XmssSegData19
import LeanVM.Guest.B1.Sig.XmssSegData20
import LeanVM.Guest.B1.Sig.XmssSegData21
import LeanVM.Guest.B1.Sig.XmssSegData22
import LeanVM.Guest.B1.Sig.XmssSegData23
import LeanVM.Guest.B1.Sig.XmssSegData24
import LeanVM.Guest.B1.Sig.XmssSegData25
import LeanVM.Guest.B1.Sig.XmssSegData26
import LeanVM.Guest.B1.Sig.XmssSegData27
import LeanVM.Guest.B1.Sig.XmssSegData28
import LeanVM.Guest.B1.Sig.XmssSegData29
import LeanVM.Guest.B1.Sig.XmssSegData30
import LeanVM.Guest.B1.Sig.XmssSegData31
import LeanVM.Guest.B1.Sig.XmssSegData32
import LeanVM.Guest.B1.Sig.XmssSegData33
import LeanVM.Guest.B1.Sig.XmssSegData34
import LeanVM.Guest.B1.Common.Basic

namespace LeanVM.Guest.B1.Sig

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

set_option maxRecDepth 100000 in
theorem l2Pre_eq : (Fn.«main_loop2».core).body.take 9 = l2Pre :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_drop_313 : ((Fn.«main_loop2».core).body.drop 9).drop 313 = (xSeg ++ l2Post).drop 313 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_0 : (((Fn.«main_loop2».core).body.drop 9).drop 0).take 70 = ((xSeg ++
    l2Post).drop
    0).take 70 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_85 : (((Fn.«main_loop2».core).body.drop 9).drop 85).take 78 = ((xSeg ++
    l2Post).drop
    85).take 78 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_164 : (((Fn.«main_loop2».core).body.drop 9).drop 164).take 3 = ((xSeg ++
    l2Post).drop 164).take 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_168 : (((Fn.«main_loop2».core).body.drop 9).drop 168).take 45 = ((xSeg ++
    l2Post).drop 168).take 45 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_228 : (((Fn.«main_loop2».core).body.drop 9).drop 228).take 78 = ((xSeg ++
    l2Post).drop 228).take 78 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_307 : (((Fn.«main_loop2».core).body.drop 9).drop 307).take 3 = ((xSeg ++
    l2Post).drop 307).take 3 :=
  stmtsEqb_sound (by decide +kernel)

set_option maxRecDepth 100000 in
theorem xSeg_slice_311 : (((Fn.«main_loop2».core).body.drop 9).drop 311).take 2 = ((xSeg ++
    l2Post).drop 311).take 2 :=
  stmtsEqb_sound (by decide +kernel)

/-- **`main_loop2`'s body**, checked by the kernel in slices: the check `xSeg` between `l2Pre` and
`l2Post`. -/
theorem loop2_split : (Fn.«main_loop2».core).body = l2Pre ++ (xSeg ++ l2Post) := by
  have h313 := xSeg_drop_313
  have h311 := drop_eq_of_take xSeg_slice_311 h313
  have h310 := drop_eq_of_take xSeg_slice_310 h311
  have h307 := drop_eq_of_take xSeg_slice_307 h310
  have h306 := drop_eq_of_take xSeg_slice_306 h307
  have h228 := drop_eq_of_take xSeg_slice_228 h306
  have h227 := drop_eq_of_take xSeg_slice_227 h228
  have h226 := drop_eq_of_take xSeg_slice_226 h227
  have h225 := drop_eq_of_take xSeg_slice_225 h226
  have h224 := drop_eq_of_take xSeg_slice_224 h225
  have h223 := drop_eq_of_take xSeg_slice_223 h224
  have h222 := drop_eq_of_take xSeg_slice_222 h223
  have h221 := drop_eq_of_take xSeg_slice_221 h222
  have h220 := drop_eq_of_take xSeg_slice_220 h221
  have h219 := drop_eq_of_take xSeg_slice_219 h220
  have h218 := drop_eq_of_take xSeg_slice_218 h219
  have h217 := drop_eq_of_take xSeg_slice_217 h218
  have h216 := drop_eq_of_take xSeg_slice_216 h217
  have h215 := drop_eq_of_take xSeg_slice_215 h216
  have h214 := drop_eq_of_take xSeg_slice_214 h215
  have h213 := drop_eq_of_take xSeg_slice_213 h214
  have h168 := drop_eq_of_take xSeg_slice_168 h213
  have h167 := drop_eq_of_take xSeg_slice_167 h168
  have h164 := drop_eq_of_take xSeg_slice_164 h167
  have h163 := drop_eq_of_take xSeg_slice_163 h164
  have h85 := drop_eq_of_take xSeg_slice_85 h163
  have h84 := drop_eq_of_take xSeg_slice_84 h85
  have h83 := drop_eq_of_take xSeg_slice_83 h84
  have h82 := drop_eq_of_take xSeg_slice_82 h83
  have h81 := drop_eq_of_take xSeg_slice_81 h82
  have h80 := drop_eq_of_take xSeg_slice_80 h81
  have h79 := drop_eq_of_take xSeg_slice_79 h80
  have h78 := drop_eq_of_take xSeg_slice_78 h79
  have h77 := drop_eq_of_take xSeg_slice_77 h78
  have h76 := drop_eq_of_take xSeg_slice_76 h77
  have h75 := drop_eq_of_take xSeg_slice_75 h76
  have h74 := drop_eq_of_take xSeg_slice_74 h75
  have h73 := drop_eq_of_take xSeg_slice_73 h74
  have h72 := drop_eq_of_take xSeg_slice_72 h73
  have h71 := drop_eq_of_take xSeg_slice_71 h72
  have h70 := drop_eq_of_take xSeg_slice_70 h71
  have h0 := drop_eq_of_take xSeg_slice_0 h70
  rw [List.drop_zero, List.drop_zero] at h0
  rw [← List.take_append_drop 9 (Fn.«main_loop2».core).body, l2Pre_eq, h0]

end
end LeanVM.Guest.B1.Sig
