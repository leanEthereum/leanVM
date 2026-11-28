import LeanVM.Guest.B1.VsC.Quiet
import LeanVM.Guest.B1.VsC.GPowerC
import LeanVM.Guest.B1.VsC.AsgC
import LeanVM.Guest.B1.VsC.Log2C
import LeanVM.Guest.B1.VsC.IndexMleC
import LeanVM.Guest.B1.VsC.RelC
import LeanVM.Guest.B1.VsC.FreeC
import LeanVM.Guest.B1.VsC.RingColsC
import LeanVM.Guest.B1.VsC.IsZeroC
import LeanVM.Guest.B1.VsC.SlowC
import LeanVM.Guest.B1.VsC.SlowA
import LeanVM.Guest.B1.VsC.LrC2
import LeanVM.Guest.B1.VsC.LrTable
import LeanVM.Guest.B1.VsC.OpenStackedA
import LeanVM.Guest.B1.VsC.LrA
import LeanVM.Guest.B1.Bits.QueryWindowsCompleteAll
import LeanVM.Guest.B1.VsC.QwCertB2C
import LeanVM.Guest.B1.VsC.LpA
import LeanVM.Guest.B1.VsC.LpComplete
import LeanVM.Guest.B1.VsC.Oq.Table
import LeanVM.Guest.B1.VsC.Oq.VmcA
import LeanVM.Guest.B1.VsC.Oq.LqMain
import LeanVM.Guest.B1.VsC.Oq.LqHints
import LeanVM.Guest.B1.VsC.Oq.LqCap

/-!
# `verify_sub`'s callees outside the link, complete, pinned

The stack's bit functions, the Keccak reduction's `index_mle`, the opening's straight callees and
the free callees, each in `CallCompletes` form. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_nodeRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_nodeRd

/-- info: 'LeanVM.Guest.B1.VsC.postQuiet_node' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.postQuiet_node

/-- info: 'LeanVM.Guest.B1.VsC.walk_quiet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.walk_quiet

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_leaf_pinned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_leaf_pinned

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_straight_ex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_straight_ex

/-- info: 'LeanVM.Guest.B1.VsC.g_power_of_word_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.g_power_of_word_complete

/-- info: 'LeanVM.Guest.B1.VsC.assert_small_g_power_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.assert_small_g_power_complete

/-- info: 'LeanVM.Guest.B1.VsC.log2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.log2_complete

/-- info: 'LeanVM.Guest.B1.VsC.index_mle_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.index_mle_complete

/-- info: 'LeanVM.Guest.B1.VsC.fold_final_msg_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.fold_final_msg_complete

/-- info: 'LeanVM.Guest.B1.VsC.opening_tail_round_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.opening_tail_round_complete

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_point_from_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_point_from_complete

/-- info: 'LeanVM.Guest.B1.VsC.eq_prefix_run_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.eq_prefix_run_complete

/-- info: 'LeanVM.Guest.B1.VsC.eq_prefix_chain_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.eq_prefix_chain_complete

/-- info: 'LeanVM.Guest.B1.VsC.rs_eq_rows_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rs_eq_rows_complete

/-- info: 'LeanVM.Guest.B1.VsC.verify_merkle_cap_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.verify_merkle_cap_complete

/-- info: 'LeanVM.Guest.B1.VsC.ring_cols_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.ring_cols_complete

/-- info: 'LeanVM.Guest.B1.VsC.is_zero_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.is_zero_complete

/-- info: 'LeanVM.Guest.B1.VsC.rqs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.rqs_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrs_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrs_complete

/-- info: 'LeanVM.Guest.B1.VsC.shapeR_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.shapeR_leaf

/-- info: 'LeanVM.Guest.B1.VsC.lp_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lp_shape

/-- info: 'LeanVM.Guest.B1.VsC.lsumA_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lsumA_complete'

/-- info: 'LeanVM.Guest.B1.VsC.lrsA_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrsA_complete'

/-- info: 'LeanVM.Guest.B1.VsC.lrsA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrsA_complete

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes0_loopFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes0_loopFlat

/-- info: 'LeanVM.Guest.B1.VsC.shapeR_loopFlat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.shapeR_loopFlat

/-- info: 'LeanVM.Guest.B1.VsC.lr1_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr1_loop

/-- info: 'LeanVM.Guest.B1.VsC.lr1_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr1_shape

/-- info: 'LeanVM.Guest.B1.VsC.lr2_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr2_loop

/-- info: 'LeanVM.Guest.B1.VsC.lr2_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr2_shape

/-- info: 'LeanVM.Guest.B1.VsC.lr_checks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr_checks

/-- info: 'LeanVM.Guest.B1.VsC.lrA_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrA_complete'

/-- info: 'LeanVM.Guest.B1.VsC.lrA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrA_complete

/-- info: 'LeanVM.Guest.B1.qw_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.qw_holds

/-- info: 'LeanVM.Guest.B1.decode_query_windows_complete_all_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.decode_query_windows_complete_all_holds

/-- info: 'LeanVM.Guest.B1.VsC.qwA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.qwA_complete

/-- info: 'LeanVM.Guest.B1.VsC.qwCert_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.qwCert_b2c

/-- info: 'LeanVM.Guest.B1.VsC.qwA_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.qwA_b2c

/-- info: 'LeanVM.Guest.B1.VsC.lpL_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lpL_complete

/-- info: 'LeanVM.Guest.B1.VsC.lpA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lpA_complete

/-- info: 'LeanVM.Guest.B1.VsC.lpA_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lpA_b2c

/-- info: 'LeanVM.Guest.B1.VsC.oqL_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.oqL_complete

/-- info: 'LeanVM.Guest.B1.VsC.oqA_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.oqA_complete'

/-- info: 'LeanVM.Guest.B1.VsC.oqA_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.oqA_all

/-- info: 'LeanVM.Guest.B1.VsC.vmcA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vmcA

/-- info: 'LeanVM.Guest.B1.VsC.lqA_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqA_all

/-- info: 'LeanVM.Guest.B1.VsC.lq_pops_sameStreams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lq_pops_sameStreams

/-- info: 'LeanVM.Guest.B1.VsC.lqCall_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqCall_static

/-- info: 'LeanVM.Guest.B1.VsC.lqCall_sameStreams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqCall_sameStreams

/-- info: 'LeanVM.Guest.B1.VsC.lqCapHonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqCapHonest
