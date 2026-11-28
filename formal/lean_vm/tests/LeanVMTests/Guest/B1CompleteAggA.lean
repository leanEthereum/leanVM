import LeanVM.Guest.Complete.Agg.Batched
import LeanVM.Guest.Complete.Agg.SumcheckA
import LeanVM.Guest.Complete.Agg.Loop1A
import LeanVM.Guest.Complete.Agg.Loop2A
import LeanVM.Guest.Complete.Agg.Loop3A
import LeanVM.Guest.Complete.Agg.Loop0A
import LeanVM.Guest.Complete.Agg.Wins
import LeanVM.Guest.Complete.Agg.Layout
import LeanVM.Guest.Complete.Agg.Calls
import LeanVM.Guest.Complete.Agg.Hon
import LeanVM.Guest.Complete.Agg.Wrap
import LeanVM.Guest.Complete.Agg.W10
import LeanVM.Guest.Complete.Agg.W46
import LeanVM.Guest.Complete.Agg.W8
import LeanVM.Guest.Complete.Agg.W0
import LeanVM.Guest.Complete.Agg.W2
import LeanVM.Guest.Complete.Agg.Compose
import LeanVM.Guest.Complete.Agg.Field
import LeanVM.Guest.Complete.Agg.Post
import LeanVM.Guest.Complete.Agg.Exact

/-!
# `aggregate_claims`' placed completeness pieces, pinned

The honest absorbing rows, the batching's converse (`batched_of_run`), the batching sumcheck
placed, and `aggregate_claims` placed from its windows' hypotheses (`atEvery_agg_of_hyp`). Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.Agg.absSt_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.absSt_rows

/-- info: 'LeanVM.Guest.Complete.Agg.absSt_last' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.absSt_last

/-- info: 'LeanVM.Guest.Complete.Agg.batched_of_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.batched_of_run

/-- info: 'LeanVM.Guest.Complete.Agg.agg_bs_callCompletesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_bs_callCompletesA

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop1_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop1_callAtA

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop2_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop2_callAtA

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop3_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop3_callAtA

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop0_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop0_callAtA

/-- info: 'LeanVM.Guest.Complete.Agg.guest_deferredVariableCount' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.guest_deferredVariableCount

/-- info: 'LeanVM.Guest.Complete.Agg.wAgg_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.wAgg_flat

/-- info: 'LeanVM.Guest.Complete.Agg.wAgg_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.wAgg_ok

/-- info: 'LeanVM.Guest.Complete.Agg.chk_aggP' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.chk_aggP

/-- info: 'LeanVM.Guest.Complete.Agg.agg_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_seg

/-- info: 'LeanVM.Guest.Complete.Agg.agg_callAtA_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_callAtA_of_hyp

/-- info: 'LeanVM.Guest.Complete.Agg.atEvery_agg_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.atEvery_agg_of_hyp

/-- info: 'LeanVM.Guest.Complete.Agg.agg_field_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_field_of_hyp

/-- info: 'LeanVM.Guest.Complete.Agg.aWalk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aWalk

/-- info: 'LeanVM.Guest.Complete.Agg.aVal_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aVal_sizes

/-- info: 'LeanVM.Guest.Complete.Agg.aAllocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aAllocs

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop0_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop0_atEvery

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop1_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop1_atEvery

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop2_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop2_atEvery

/-- info: 'LeanVM.Guest.Complete.Agg.agg_loop3_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_loop3_atEvery

/-- info: 'LeanVM.Guest.Complete.Agg.agg_bs_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_bs_atEvery

/-- info: 'LeanVM.Guest.Complete.Agg.callAtA_wrap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.callAtA_wrap

/-- info: 'LeanVM.Guest.Complete.Agg.agg_field_of_hypB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_field_of_hypB

/-- info: 'LeanVM.Guest.Complete.Agg.rd_eq_rdW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.rd_eq_rdW

/-- info: 'LeanVM.Guest.Complete.Agg.aLists_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aLists_length

/-- info: 'LeanVM.Guest.Complete.Agg.aWo_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aWo_in

/-- info: 'LeanVM.Guest.Complete.Agg.aV_ptrs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aV_ptrs

/-- info: 'LeanVM.Guest.Complete.Agg.aLoad_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aLoad_fresh

/-- info: 'LeanVM.Guest.Complete.Agg.valAt_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.valAt_own

/-- info: 'LeanVM.Guest.Complete.Agg.aBatched_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aBatched_facts

/-- info: 'LeanVM.Guest.Complete.Agg.aWsum_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aWsum_full

/-- info: 'LeanVM.Guest.Complete.Agg.holds_aAll' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.holds_aAll

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w10' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w10

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w4

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w6' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w6

/-- info: 'LeanVM.Guest.Complete.Agg.own_fresh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.own_fresh

/-- info: 'LeanVM.Guest.Complete.Agg.own_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.own_store

/-- info: 'LeanVM.Guest.Complete.Agg.aB_succ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aB_succ

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w8

/-- info: 'LeanVM.Guest.Complete.Agg.fresh_len' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.fresh_len

/-- info: 'LeanVM.Guest.Complete.Agg.w0_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w0_row

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w0

/-- info: 'LeanVM.Guest.Complete.Agg.aggAbs_pend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggAbs_pend

/-- info: 'LeanVM.Guest.Complete.Agg.w2_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_row

/-- info: 'LeanVM.Guest.Complete.Agg.w2_perm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_perm

/-- info: 'LeanVM.Guest.Complete.Agg.w2_nonce' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_nonce

/-- info: 'LeanVM.Guest.Complete.Agg.w2_col' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_col

/-- info: 'LeanVM.Guest.Complete.Agg.w2_cap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_cap

/-- info: 'LeanVM.Guest.Complete.Agg.aTree_lvl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aTree_lvl

/-- info: 'LeanVM.Guest.Complete.Agg.w2_treeV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_treeV

/-- info: 'LeanVM.Guest.Complete.Agg.w2_grindT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.w2_grindT

/-- info: 'LeanVM.Guest.Complete.Agg.runHypT_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.runHypT_w2

/-- info: 'LeanVM.Guest.Complete.Agg.aggWinHyp_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggWinHyp_of_left

/-- info: 'LeanVM.Guest.Complete.Agg.agg_fieldB_of_left' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_fieldB_of_left

/-- info: 'LeanVM.Guest.Complete.Agg.agg_bs_atEvery'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_bs_atEvery'

/-- info: 'LeanVM.Guest.Complete.Agg.agg_reg0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_reg0

/-- info: 'LeanVM.Guest.Complete.Agg.agg_reg1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_reg1

/-- info: 'LeanVM.Guest.Complete.Agg.agg_reg2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_reg2

/-- info: 'LeanVM.Guest.Complete.Agg.agg_regbs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_regbs

/-- info: 'LeanVM.Guest.Complete.Agg.agg_reg3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_reg3

/-- info: 'LeanVM.Guest.Complete.Agg.childWords' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.childWords

/-- info: 'LeanVM.Guest.Complete.Agg.agg_pre0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_pre0

/-- info: 'LeanVM.Guest.Complete.Agg.agg_pre1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_pre1

/-- info: 'LeanVM.Guest.Complete.Agg.agg_pre2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_pre2

/-- info: 'LeanVM.Guest.Complete.Agg.agg_bs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_bs

/-- info: 'LeanVM.Guest.Complete.Agg.aEqc565' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aEqc565

/-- info: 'LeanVM.Guest.Complete.Agg.agg_pre3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_pre3

/-- info: 'LeanVM.Guest.Complete.Agg.aggLeftAt_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggLeftAt_of_post

/-- info: 'LeanVM.Guest.Complete.Agg.agg_field_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_field_of_post

/-- info: 'LeanVM.Guest.Complete.Agg.agg_field_alW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_field_alW

/-- info: 'LeanVM.Guest.Complete.Agg.agg_kOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_kOk

/-- info: 'LeanVM.Guest.Complete.Agg.msgs_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.msgs_words

/-- info: 'LeanVM.Guest.Complete.Agg.aggK_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggK_of

/-- info: 'LeanVM.Guest.Complete.Agg.agg_pop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_pop

/-- info: 'LeanVM.Guest.Complete.Agg.aggPost_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggPost_of_exact

/-- info: 'LeanVM.Guest.Complete.Agg.aggPostHyp_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggPostHyp_of_exact

/-- info: 'LeanVM.Guest.Complete.Agg.agg_field_alW_of_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.agg_field_alW_of_exact

/-- info: 'LeanVM.Guest.Complete.Agg.aggP_computed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggP_computed

/-- info: 'LeanVM.Guest.Complete.Agg.gcInline_exact_of_wins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.gcInline_exact_of_wins

/-- info: 'LeanVM.Guest.Complete.Agg.aV_win' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aV_win

/-- info: 'LeanVM.Guest.Complete.Agg.aggExactAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggExactAt

/-- info: 'LeanVM.Guest.Complete.Agg.aggExactHyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggExactHyp

/-- info: 'LeanVM.Guest.Complete.Agg.aggField' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggField

/-- info: 'LeanVM.Guest.Complete.Agg.aggField_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.Agg.aggField_honest
