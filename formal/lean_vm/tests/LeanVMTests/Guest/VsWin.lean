import LeanVM.Guest.B1.VsC.WinSeg
import LeanVM.Guest.B1.VsC.VsEval
import LeanVM.Guest.B1.VsC.VsW0
import LeanVM.Guest.B1.VsC.VsW1
import LeanVM.Guest.B1.VsC.VsW2
import LeanVM.Guest.B1.VsC.VsW3
import LeanVM.Guest.B1.VsC.WinGen
import LeanVM.Guest.B1.VsC.VsWins
import LeanVM.Guest.B1.VsC.LeavesA
import LeanVM.Guest.B1.VsC.IndexSideA
import LeanVM.Guest.B1.VsC.VsPh1
import LeanVM.Guest.B1.VsC.VsSel
import LeanVM.Guest.B1.VsC.VsPh2
import LeanVM.Guest.B1.VsC.VsPh2W
import LeanVM.Guest.B1.VsC.VsPh3
import LeanVM.Guest.B1.VsC.LeafEnd
import LeanVM.Guest.B1.VsC.VsFront
import LeanVM.Guest.B1.VsC.VsPh4
import LeanVM.Guest.B1.VsC.GrindRun
import LeanVM.Guest.B1.VsC.VsPh5
import LeanVM.Guest.B1.VsC.VsPh6
import LeanVM.Guest.B1.VsC.RunBufs
import LeanVM.Guest.B1.VsC.VsRunData
import LeanVM.Guest.B1.VsC.VsPh7
import LeanVM.Guest.B1.VsC.VsPh8
import LeanVM.Guest.B1.VsC.VsPh9
import LeanVM.Guest.B1.VsC.VsPh10
import LeanVM.Guest.B1.VsC.VsPh11
import LeanVM.Guest.B1.VsC.VsPh13

/-!
# `verify_sub`'s windows, pinned

The window kinds, the forward valuation through the branches, the windows proved. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.segA_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_atoms

/-- info: 'LeanVM.Guest.B1.VsC.segA_call1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_call1

/-- info: 'LeanVM.Guest.B1.VsC.walk_dispatch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.walk_dispatch

/-- info: 'LeanVM.Guest.B1.VsC.segA_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_ite

/-- info: 'LeanVM.Guest.B1.VsC.vsBody_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsBody_eq

/-- info: 'LeanVM.Guest.B1.VsC.vs_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_loop

/-- info: 'LeanVM.Guest.B1.VsC.chk_vsC' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chk_vsC

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_params' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_params

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodA

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodI1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodI1

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodB

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodI2z' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodI2z

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodI2n' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodI2n

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_goodC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_goodC

/-- info: 'LeanVM.Guest.B1.VsC.holds_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_plain

/-- info: 'LeanVM.Guest.B1.VsC.holds_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_rc

/-- info: 'LeanVM.Guest.B1.VsC.vsW0_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW0_eq

/-- info: 'LeanVM.Guest.B1.VsC.vsW0_54' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW0_54

/-- info: 'LeanVM.Guest.B1.VsC.vsW0_segA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW0_segA

/-- info: 'LeanVM.Guest.B1.VsC.hint_stream_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.hint_stream_completeA

/-- info: 'LeanVM.Guest.B1.VsC.vsW1_segA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW1_segA

/-- info: 'LeanVM.Guest.B1.VsC.holds_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_run

/-- info: 'LeanVM.Guest.B1.VsC.holds_loadAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_loadAt

/-- info: 'LeanVM.Guest.B1.VsC.holds_storeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_storeAt

/-- info: 'LeanVM.Guest.B1.VsC.vsW2_segA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW2_segA

/-- info: 'LeanVM.Guest.B1.VsC.g_power_of_word_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.g_power_of_word_completeA

/-- info: 'LeanVM.Guest.B1.VsC.callCompletesA_of_noMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletesA_of_noMem

/-- info: 'LeanVM.Guest.B1.VsC.vsW3_segA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW3_segA

/-- info: 'LeanVM.Guest.B1.VsC.segA_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_run

/-- info: 'LeanVM.Guest.B1.VsC.holds_fact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_fact

/-- info: 'LeanVM.Guest.B1.VsC.segA_callW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_callW

/-- info: 'LeanVM.Guest.B1.VsC.segA_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.segA_wins

/-- info: 'LeanVM.Guest.B1.VsC.seg_bind' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.seg_bind

/-- info: 'LeanVM.Guest.B1.VsC.seg_ite' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.seg_ite

/-- info: 'LeanVM.Guest.B1.VsC.callAt_of_completesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callAt_of_completesA

/-- info: 'LeanVM.Guest.B1.VsC.vsRcs_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsRcs_eq

/-- info: 'LeanVM.Guest.B1.VsC.wA_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wA_flat

/-- info: 'LeanVM.Guest.B1.VsC.wB_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wB_flat

/-- info: 'LeanVM.Guest.B1.VsC.wC_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wC_flat

/-- info: 'LeanVM.Guest.B1.VsC.wA_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wA_ok

/-- info: 'LeanVM.Guest.B1.VsC.wC_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.wC_ok

/-- info: 'LeanVM.Guest.B1.VsC.vs_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_seg

/-- info: 'LeanVM.Guest.B1.VsC.vsWindowsA_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindowsA_of_hyp

/-- info: 'LeanVM.Guest.B1.VsC.vsWindowsFromCallees_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsWindowsFromCallees_of_hyp

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_append

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_call_of_completesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_call_of_completesA

/-- info: 'LeanVM.Guest.B1.VsC.callCompletesA_leafIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletesA_leafIn

/-- info: 'LeanVM.Guest.B1.VsC.table_size_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.table_size_completeA

/-- info: 'LeanVM.Guest.B1.VsC.chunk_d_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chunk_d_completeA

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_point_from_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_point_from_leafA

/-- info: 'LeanVM.Guest.B1.VsC.opening_message_L1_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.opening_message_L1_leafA

/-- info: 'LeanVM.Guest.B1.VsC.state_ends_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.state_ends_leafA

/-- info: 'LeanVM.Guest.B1.VsC.one_plus_suffixes_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.one_plus_suffixes_leafA

/-- info: 'LeanVM.Guest.B1.VsC.packed_message_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.packed_message_leafA

/-- info: 'LeanVM.Guest.B1.VsC.table_point_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.table_point_leafA

/-- info: 'LeanVM.Guest.B1.VsC.assert_small_g_power_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.assert_small_g_power_completeA

/-- info: 'LeanVM.Guest.B1.VsC.is_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.is_shape

/-- info: 'LeanVM.Guest.B1.VsC.index_side_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.index_side_completeA

/-- info: 'LeanVM.Guest.B1.VsC.RunHyp.of_asks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.RunHyp.of_asks

/-- info: 'LeanVM.Guest.B1.VsC.vsW0_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW0_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsW2_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW2_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsPh0_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh0_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsW4_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW4_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsW6_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW6_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsPh1_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh1_wins

/-- info: 'LeanVM.Guest.B1.VsC.vs_sel234' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vs_sel234

/-- info: 'LeanVM.Guest.B1.VsC.vsW18_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW18_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.tsChk_pureF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tsChk_pureF

/-- info: 'LeanVM.Guest.B1.VsC.tsRun_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tsRun_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.tsRun0_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tsRun0_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.ts_disp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ts_disp

/-- info: 'LeanVM.Guest.B1.VsC.vsA_w7_17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsA_w7_17

/-- info: 'LeanVM.Guest.B1.VsC.vsI1n_atoms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsI1n_atoms

/-- info: 'LeanVM.Guest.B1.VsC.vsW6_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsW6_vals

/-- info: 'LeanVM.Guest.B1.VsC.ts_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ts_pair

/-- info: 'LeanVM.Guest.B1.VsC.ts_pair0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ts_pair0

/-- info: 'LeanVM.Guest.B1.VsC.vsPh2_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh2_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsPh2_sel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh2_sel

/-- info: 'LeanVM.Guest.B1.VsC.cb_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cb_vals

/-- info: 'LeanVM.Guest.B1.VsC.vsB0_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsB0_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsB2_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsB2_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsZ_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsZ_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsNa_runHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsNa_runHyp

/-- info: 'LeanVM.Guest.B1.VsC.vsPh3_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh3_wins

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_call_of_completesA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_call_of_completesA_le

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_216' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_216

/-- info: 'LeanVM.Guest.B1.VsC.leafAtA_of_callCompletes0_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.leafAtA_of_callCompletes0_leaf

/-- info: 'LeanVM.Guest.B1.VsC.LeafAtA.completesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.LeafAtA.completesA

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_call_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_call_at

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_call_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_call_leaf

/-- info: 'LeanVM.Guest.B1.VsC.leafAtA_of_noMem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.leafAtA_of_noMem

/-- info: 'LeanVM.Guest.B1.VsC.g_power_of_word_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.g_power_of_word_leafA

/-- info: 'LeanVM.Guest.B1.VsC.leafAtA_leafIn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.leafAtA_leafIn

/-- info: 'LeanVM.Guest.B1.VsC.table_size_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.table_size_leafA

/-- info: 'LeanVM.Guest.B1.VsC.chunk_d_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chunk_d_leafA

/-- info: 'LeanVM.Guest.B1.VsC.assert_small_g_power_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.assert_small_g_power_leafA

/-- info: 'LeanVM.Guest.B1.VsC.vsFront_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsFront_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_483' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_483

/-- info: 'LeanVM.Guest.B1.VsC.vsPh4_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh4_wins

/-- info: 'LeanVM.Guest.B1.VsC.gcO_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.gcO_atoms

/-- info: 'LeanVM.Guest.B1.VsC.vsPh5_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh5_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsPh6_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh6_wins

/-- info: 'LeanVM.Guest.B1.VsC.runHyp_bufs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.runHyp_bufs

/-- info: 'LeanVM.Guest.B1.VsC.holds_bufs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.holds_bufs

/-- info: 'LeanVM.Guest.B1.VsC.winsHyp_run_bufs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.winsHyp_run_bufs

/-- info: 'LeanVM.Guest.B1.VsC.pkC_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.pkC_eq

/-- info: 'LeanVM.Guest.B1.VsC.vsPh7_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh7_wins

/-- info: 'LeanVM.Guest.B1.VsC.index_side_atA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.index_side_atA

/-- info: 'LeanVM.Guest.B1.VsC.vsPh8_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh8_wins

/-- info: 'LeanVM.Guest.B1.VsC.readsAt_drop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.readsAt_drop

/-- info: 'LeanVM.Guest.B1.VsC.vsPh9_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh9_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsPh10_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh10_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsVal_679' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsVal_679

/-- info: 'LeanVM.Guest.B1.VsC.vsPh11_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh11_wins

/-- info: 'LeanVM.Guest.B1.VsC.tp_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tp_step

/-- info: 'LeanVM.Guest.B1.VsC.vsPh12_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh12_wins

/-- info: 'LeanVM.Guest.B1.VsC.split_inK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.split_inK

/-- info: 'LeanVM.Guest.B1.VsC.vsPh13_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh13_wins

/-- info: 'LeanVM.Guest.B1.VsC.vsPh12_13_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsPh12_13_wins
