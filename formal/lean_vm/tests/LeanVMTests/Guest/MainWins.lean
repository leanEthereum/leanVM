import LeanVM.Guest.Complete.MainWinGen
import LeanVM.Guest.Complete.MainWins
import LeanVM.Guest.Complete.MainRunFacts
import LeanVM.Guest.Complete.MainWinCall
import LeanVM.Guest.Complete.MainWords
import LeanVM.Guest.Complete.MainOrc
import LeanVM.Guest.Complete.MainHypAt
import LeanVM.Guest.Complete.MainRuns
import LeanVM.Guest.Complete.MainBytes
import LeanVM.Guest.Complete.MainPreWins
import LeanVM.Guest.Complete.ClaimCells
import LeanVM.Guest.Complete.MainPreChain
import LeanVM.Guest.Complete.MainRest
import LeanVM.Guest.Complete.MainDaWins
import LeanVM.Guest.Complete.MainMid
import LeanVM.Guest.Complete.MainMidWins
import LeanVM.Guest.Complete.MainKids
import LeanVM.Guest.Complete.MainMidTail
import LeanVM.Guest.Complete.MainLeafAgg
import LeanVM.Guest.Complete.MainPostWins
import LeanVM.Guest.Complete.MainFinal

/-!
# `main`'s windows, pinned

The window kinds over temporaries, `main`'s generated windows and their composition. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.segA_runT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_runT

/-- info: 'LeanVM.Guest.Complete.segA_callWT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_callWT

/-- info: 'LeanVM.Guest.Complete.segA_winsT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_winsT

/-- info: 'LeanVM.Guest.Complete.seg_iteT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.seg_iteT

/-- info: 'LeanVM.Guest.Complete.winsHypT_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_append

/-- info: 'LeanVM.Guest.Complete.wPre_flat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.wPre_flat

/-- info: 'LeanVM.Guest.Complete.wPre_ok' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.wPre_ok

/-- info: 'LeanVM.Guest.Complete.main_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_seg

/-- info: 'LeanVM.Guest.Complete.mainWindowAt_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowAt_of_hyp

/-- info: 'LeanVM.Guest.Complete.mainWindowFromCallees_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowFromCallees_of_hyp

/-- info: 'LeanVM.Guest.Complete.guard_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.guard_eq_zero_iff

/-- info: 'LeanVM.Guest.Complete.mDa_keccak' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mDa_keccak

/-- info: 'LeanVM.Guest.Complete.da_cells_digest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_cells_digest

/-- info: 'LeanVM.Guest.Complete.mDa_own' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mDa_own

/-- info: 'LeanVM.Guest.Complete.winsHypT_call_of_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_call_of_atEvery

/-- info: 'LeanVM.Guest.Complete.winsHypT_cif_of_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_cif_of_atEvery

/-- info: 'LeanVM.Guest.Complete.mVal_meta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_meta

/-- info: 'LeanVM.Guest.Complete.mVal_guards' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_guards

/-- info: 'LeanVM.Guest.Complete.mVal_guard_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_guard_zero_iff

/-- info: 'LeanVM.Guest.Complete.memT_touch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.memT_touch

/-- info: 'LeanVM.Guest.Complete.memT_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.memT_rc

/-- info: 'LeanVM.Guest.Complete.pureT_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.pureT_rc

/-- info: 'LeanVM.Guest.Complete.holdsWords_rdW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsWords_rdW

/-- info: 'LeanVM.Guest.Complete.isSome_of_inW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.isSome_of_inW

/-- info: 'LeanVM.Guest.Complete.mainLists_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainLists_length

/-- info: 'LeanVM.Guest.Complete.mainWords_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWords_eq

/-- info: 'LeanVM.Guest.Complete.mainWords_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWords_in

/-- info: 'LeanVM.Guest.Complete.mainWords_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWords_cover

/-- info: 'LeanVM.Guest.Complete.fs_main_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.fs_main_lt

/-- info: 'LeanVM.Guest.Complete.slots_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.slots_lt

/-- info: 'LeanVM.Guest.Complete.mEs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mEs_eq

/-- info: 'LeanVM.Guest.Complete.mAllocs_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mAllocs_eq

/-- info: 'LeanVM.Guest.Complete.mOrc_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mOrc_counts

/-- info: 'LeanVM.Guest.Complete.mOrc_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mOrc_sizes

/-- info: 'LeanVM.Guest.Complete.mAllocs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mAllocs

/-- info: 'LeanVM.Guest.Complete.slots_eq_cov' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.slots_eq_cov

/-- info: 'LeanVM.Guest.Complete.kidBase_all' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidBase_all

/-- info: 'LeanVM.Guest.Complete.raw_le_slots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.raw_le_slots

/-- info: 'LeanVM.Guest.Complete.count_def' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.count_def

/-- info: 'LeanVM.Guest.Complete.winsHypT_call_of_atEvery'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_call_of_atEvery'

/-- info: 'LeanVM.Guest.Complete.winsHypT_cif_of_atEvery'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_cif_of_atEvery'

/-- info: 'LeanVM.Guest.Complete.mainWinHyp_of_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHyp_of_at

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_at

/-- info: 'LeanVM.Guest.Complete.plain_fields' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.plain_fields

/-- info: 'LeanVM.Guest.Complete.runHypT_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_plain

/-- info: 'LeanVM.Guest.Complete.forall_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.forall_split

/-- info: 'LeanVM.Guest.Complete.w0_rcs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.w0_rcs

/-- info: 'LeanVM.Guest.Complete.runHypT_w0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_w0

/-- info: 'LeanVM.Guest.Complete.heapHintAddrs_noHeap' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.heapHintAddrs_noHeap

/-- info: 'LeanVM.Guest.Complete.own_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.own_main

/-- info: 'LeanVM.Guest.Complete.allocs_atoms' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.allocs_atoms

/-- info: 'LeanVM.Guest.Complete.runHypT_w9' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_w9

/-- info: 'LeanVM.Guest.Complete.winsHypT_w1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_w1

/-- info: 'LeanVM.Guest.Complete.runHypT_w2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_w2

/-- info: 'LeanVM.Guest.Complete.winsHypT_w3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_w3

/-- info: 'LeanVM.Guest.Complete.winsHypT_w4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_w4

/-- info: 'LeanVM.Guest.Complete.fresh_shape_of_verifyDeferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.fresh_shape_of_verifyDeferred

/-- info: 'LeanVM.Guest.Complete.claimCells_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.claimCells_of

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_hyp

/-- info: 'LeanVM.Guest.Complete.winsHypT_cifI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_cifI

/-- info: 'LeanVM.Guest.Complete.runHypT_w13' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_w13

/-- info: 'LeanVM.Guest.Complete.mOrc_tags' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mOrc_tags

/-- info: 'LeanVM.Guest.Complete.wPre_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.wPre_hyp

/-- info: 'LeanVM.Guest.Complete.mainHypAt_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainHypAt_of_rest

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_rest

/-- info: 'LeanVM.Guest.Complete.mOrc_384_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mOrc_384_zero

/-- info: 'LeanVM.Guest.Complete.runHypT_daLoads' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_daLoads

/-- info: 'LeanVM.Guest.Complete.da_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_hyp

/-- info: 'LeanVM.Guest.Complete.mainRestAt_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainRestAt_of_mid

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_mid' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_mid

/-- info: 'LeanVM.Guest.Complete.winsHypT_mid0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_mid0

/-- info: 'LeanVM.Guest.Complete.mKidHyps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mKidHyps

/-- info: 'LeanVM.Guest.Complete.kidPushes_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidPushes_eq

/-- info: 'LeanVM.Guest.Complete.winsHypT_mid1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_mid1

/-- info: 'LeanVM.Guest.Complete.mRd0_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mRd0_holds

/-- info: 'LeanVM.Guest.Complete.runHypT_mid2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_mid2

/-- info: 'LeanVM.Guest.Complete.winsHypT_mid2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.winsHypT_mid2

/-- info: 'LeanVM.Guest.Complete.mainMidAt_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainMidAt_of_tail

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_tail

/-- info: 'LeanVM.Guest.Complete.leaf_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.leaf_cells

/-- info: 'LeanVM.Guest.Complete.runHypT_leaf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.runHypT_leaf

/-- info: 'LeanVM.Guest.Complete.leafAgg_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.leafAgg_hyp

/-- info: 'LeanVM.Guest.Complete.mainTailAt_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainTailAt_of_post

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_post

/-- info: 'LeanVM.Guest.Complete.daPick_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.daPick_cases

/-- info: 'LeanVM.Guest.Complete.daPick_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.daPick_cells

/-- info: 'LeanVM.Guest.Complete.mRd0_header' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mRd0_header

/-- info: 'LeanVM.Guest.Complete.post_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.post_vals

/-- info: 'LeanVM.Guest.Complete.wPost_hyp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.wPost_hyp

/-- info: 'LeanVM.Guest.Complete.mainPostAt_of_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainPostAt_of_final

/-- info: 'LeanVM.Guest.Complete.mainWinHypFromCallees_of_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWinHypFromCallees_of_final

/-- info: 'LeanVM.Guest.Complete.mainWindowFromCallees_of_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowFromCallees_of_final

/-- info: 'LeanVM.Guest.Complete.splice_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.splice_skel

/-- info: 'LeanVM.Guest.Complete.straight_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.straight_skel

/-- info: 'LeanVM.Guest.Complete.skelPops_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.skelPops_streams

/-- info: 'LeanVM.Guest.Complete.kOk_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kOk_kids

/-- info: 'LeanVM.Guest.Complete.straight_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.straight_taken

/-- info: 'LeanVM.Guest.Complete.walk_mainSs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.walk_mainSs

/-- info: 'LeanVM.Guest.Complete.mainEvs_skel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainEvs_skel

/-- info: 'LeanVM.Guest.Complete.mainEvs_taken' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainEvs_taken

/-- info: 'LeanVM.Guest.Complete.exactAt_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.exactAt_main

/-- info: 'LeanVM.Guest.Complete.kOk_main' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kOk_main

/-- info: 'LeanVM.Guest.Complete.meta_words' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.meta_words

/-- info: 'LeanVM.Guest.Complete.kidPushes_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidPushes_names

/-- info: 'LeanVM.Guest.Complete.daHints_names' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.daHints_names

/-- info: 'LeanVM.Guest.Complete.main_reorder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_reorder

/-- info: 'LeanVM.Guest.Complete.honest_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honest_eq

/-- info: 'LeanVM.Guest.Complete.main_streams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.main_streams

/-- info: 'LeanVM.Guest.Complete.mainFinalAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainFinalAt

/-- info: 'LeanVM.Guest.Complete.mainFinalFromCallees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainFinalFromCallees

/-- info: 'LeanVM.Guest.Complete.mainWindowFromCallees' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainWindowFromCallees
