import LeanVM.Guest.B1.VsC.Shape
import LeanVM.Guest.B1.VsC.CapDepth
import LeanVM.Guest.B1.VsC.LinkShape
import LeanVM.Guest.B1.VsC.ChunkDC
import LeanVM.Guest.B1.VsC.StackOrder
import LeanVM.Guest.B1.VsC.StreamChunks
import LeanVM.Guest.B1.VsC.StateEndsC
import LeanVM.Guest.B1.VsC.SuffixesC
import LeanVM.Guest.B1.VsC.TableSizeC
import LeanVM.Guest.B1.VsC.TablePointC
import LeanVM.Guest.B1.VsC.PackedMessageC
import LeanVM.Guest.B1.VsC.OpeningMessageC
import LeanVM.Guest.B1.VsC.SqueezePackedLastC
import LeanVM.Guest.B1.VsC.HintStreamC
import LeanVM.Guest.B1.VsC.IndexSideC
import LeanVM.Guest.B1.VsC.LinkCallees
import LeanVM.Guest.B1.VsC.FreeBlock
import LeanVM.Guest.B1.VsC.RoundsLastC
import LeanVM.Guest.Complete.ComposeRd
import LeanVM.Guest.Complete.SegA
import LeanVM.Guest.B1.VsC.LinkCalleesA
import LeanVM.Guest.B1.VsC.CalleesA
import LeanVM.Guest.B1.VsC.RowSideA
import LeanVM.Guest.B1.VsC.TerminalA
import LeanVM.Guest.B1.VsC.SqueezePackedA
import LeanVM.Guest.B1.VsC.RoundsSpecA
import LeanVM.Guest.B1.VsC.RoundsSpecA1

/-!
# `verify_sub`'s completeness, the layout-free pieces, pinned

An accepted child's announced layout is its run's and has the shape `verify_sub` checks; the honest
Merkle hints' cap depth is the guest's at every opening shape. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.accepted_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.accepted_rest

/-- info: 'LeanVM.Guest.B1.VsC.vsShape_of_verifyDeferred' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsShape_of_verifyDeferred

/-- info: 'LeanVM.Guest.B1.VsC.VsShape.height_least' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsShape.height_least

/-- info: 'LeanVM.Guest.B1.VsC.VsShape.height_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsShape.height_le

/-- info: 'LeanVM.Guest.B1.VsC.capDepth_honest' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.capDepth_honest

/-- info: 'LeanVM.Guest.B1.VsC.chunkD_range' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chunkD_range

/-- info: 'LeanVM.Guest.B1.VsC.packedChallenges_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.packedChallenges_eq

/-- info: 'LeanVM.Guest.B1.VsC.chal_fits' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chal_fits

/-- info: 'LeanVM.Guest.B1.VsC.chunk_d_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chunk_d_complete

/-- info: 'LeanVM.Guest.B1.VsC.honestOrder_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.honestOrder_ok

/-- info: 'LeanVM.Guest.B1.VsC.stackGroups_facts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.stackGroups_facts

/-- info: 'LeanVM.Guest.B1.VsC.streamChunks_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.streamChunks_ok

/-- info: 'LeanVM.Guest.B1.VsC.state_ends_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.state_ends_complete

/-- info: 'LeanVM.Guest.B1.VsC.one_plus_suffixes_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.one_plus_suffixes_complete

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_straightRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_straightRd

/-- info: 'LeanVM.Guest.B1.VsC.table_size_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.table_size_complete

/-- info: 'LeanVM.Guest.B1.VsC.tsLeadRest_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.tsLeadRest_iff

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_pure

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_of_rel_straight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_of_rel_straight

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_stores' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_stores

/-- info: 'LeanVM.Guest.B1.VsC.table_point_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.table_point_complete

/-- info: 'LeanVM.Guest.B1.VsC.packed_message_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.packed_message_complete

/-- info: 'LeanVM.Guest.B1.VsC.opening_message_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.opening_message_complete

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_last_L0_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_last_L0_complete

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_last_L1_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_last_L1_complete

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_last_L2_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_last_L2_complete

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_last_L3_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_last_L3_complete

/-- info: 'LeanVM.Guest.B1.VsC.hint_stream_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.hint_stream_complete

/-- info: 'LeanVM.Guest.B1.VsC.index_side_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.index_side_complete

/-- info: 'LeanVM.Guest.B1.VsC.callCompletes_storesCalls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callCompletes_storesCalls

/-- info: 'LeanVM.Guest.B1.VsC.link_row_side_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_row_side_complete

/-- info: 'LeanVM.Guest.B1.VsC.link_row_side_L6_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_row_side_L6_complete

/-- info: 'LeanVM.Guest.B1.VsC.link_row_side_L7_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_row_side_L7_complete

/-- info: 'LeanVM.Guest.B1.VsC.link_row_side_L8_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_row_side_L8_complete

/-- info: 'LeanVM.Guest.B1.VsC.link_row_side_L9_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_row_side_L9_complete

/-- info: 'LeanVM.Guest.B1.VsC.VsLinkCallees.row_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsLinkCallees.row_side

/-- info: 'LeanVM.Guest.B1.VsC.exists_free_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.exists_free_block

/-- info: 'LeanVM.Guest.B1.VsC.roundStep_det' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.roundStep_det

/-- info: 'LeanVM.Guest.B1.VsC.lrRounds_complete0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrRounds_complete0

/-- info: 'LeanVM.Guest.B1.VsC.lrl_L10_L1_L0_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_L10_L1_L0_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrl_L7_L0_L3_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_L7_L0_L3_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrl_L1_L0_L1_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_L1_L0_L1_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrRounds_complete1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrRounds_complete1

/-- info: 'LeanVM.Guest.B1.VsC.lrl_L8_L1_L1_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_L8_L1_L1_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrl_L10_L1_L3_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_L10_L1_L3_complete

/-- info: 'LeanVM.Guest.Complete.callAtA_nodeRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_nodeRd

/-- info: 'LeanVM.Guest.Complete.callAtA_nodeLRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_nodeLRd

/-- info: 'LeanVM.Guest.Complete.kidsAtF_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsAtF_mono

/-- info: 'LeanVM.Guest.Complete.kidsAtF_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidsAtF_append

/-- info: 'LeanVM.Guest.Complete.segA_append' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_append

/-- info: 'LeanVM.Guest.Complete.segA_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_nil

/-- info: 'LeanVM.Guest.Complete.callAtA_segRd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_segRd

/-- info: 'LeanVM.Guest.B1.VsC.vsComplete_of_windowsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsComplete_of_windowsA

/-- info: 'LeanVM.Guest.B1.VsC.vsComplete_of_calleesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsComplete_of_calleesA

/-- info: 'LeanVM.Guest.B1.VsC.lrs_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrs_completeA

/-- info: 'LeanVM.Guest.B1.VsC.VsLinkCalleesA.row_side' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.VsLinkCalleesA.row_side

/-- info: 'LeanVM.Guest.B1.VsC.eqtreeAt_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.eqtreeAt_complete

/-- info: 'LeanVM.Guest.B1.VsC.lt_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lt_placed

/-- info: 'LeanVM.Guest.B1.VsC.link_terminal_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_terminal_completeA

/-- info: 'LeanVM.Guest.B1.VsC.spPerms_fwd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.spPerms_fwd

/-- info: 'LeanVM.Guest.B1.VsC.spl_complete0_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.spl_complete0_all

/-- info: 'LeanVM.Guest.B1.VsC.callAtA_leaf0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.callAtA_leaf0

/-- info: 'LeanVM.Guest.B1.VsC.splA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.splA

/-- info: 'LeanVM.Guest.B1.VsC.spL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.spL_callAtA

/-- info: 'LeanVM.Guest.B1.VsC.squeeze_packed_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.squeeze_packed_completeA

/-- info: 'LeanVM.Guest.B1.VsC.chain_cur' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chain_cur

/-- info: 'LeanVM.Guest.B1.VsC.lrRounds_loads0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrRounds_loads0

/-- info: 'LeanVM.Guest.B1.VsC.lrl_placed0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_placed0

/-- info: 'LeanVM.Guest.B1.VsC.lrL_callAtA0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrL_callAtA0

/-- info: 'LeanVM.Guest.B1.VsC.chain_words_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.chain_words_le

/-- info: 'LeanVM.Guest.B1.VsC.lr_main_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lr_main_placed

/-- info: 'LeanVM.Guest.B1.VsC.lrLoopA0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrLoopA0

/-- info: 'LeanVM.Guest.B1.VsC.lrLastA_placed0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrLastA_placed0

/-- info: 'LeanVM.Guest.B1.VsC.lrLastA_copy0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrLastA_copy0

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L1_L0_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L1_L0_completeA

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L6_L0_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L6_L0_completeA

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L7_L0_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L7_L0_completeA

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L8_L1_completeA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L8_L1_completeA_of

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L9_L1_completeA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L9_L1_completeA_of

/-- info: 'LeanVM.Guest.B1.VsC.link_rounds_L10_L1_completeA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.link_rounds_L10_L1_completeA_of

/-- info: 'LeanVM.Guest.B1.VsC.vsLinkCalleesA_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsLinkCalleesA_of

/-- info: 'LeanVM.Guest.B1.VsC.gcInlineT_load_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.gcInlineT_load_one

/-- info: 'LeanVM.Guest.B1.VsC.gcPtrs_of_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.gcPtrs_of_vals

/-- info: 'LeanVM.Guest.B1.VsC.lrRound_complete1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrRound_complete1

/-- info: 'LeanVM.Guest.B1.VsC.lrRounds_loads1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrRounds_loads1

/-- info: 'LeanVM.Guest.B1.VsC.lrl_placed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrl_placed1

/-- info: 'LeanVM.Guest.B1.VsC.lrLastA_placed1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrLastA_placed1

/-- info: 'LeanVM.Guest.B1.VsC.lrL_step1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrL_step1

/-- info: 'LeanVM.Guest.B1.VsC.lrL_callAtA1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrL_callAtA1

/-- info: 'LeanVM.Guest.B1.VsC.lrLoopA1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrLoopA1

/-- info: 'LeanVM.Guest.B1.VsC.linkGrindLeft_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.linkGrindLeft_complete

/-- info: 'LeanVM.Guest.B1.VsC.vsLinkCalleesA_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsLinkCalleesA_complete

/-- info: 'LeanVM.Guest.B1.VsC.vsCalleesCompleteA_of_rest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.vsCalleesCompleteA_of_rest
