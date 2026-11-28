import LeanVM.Guest.B1.VsC.Oq.LqMain
import LeanVM.Guest.B1.VsC.Os.CHonest
import LeanVM.Guest.B1.VsC.Os.WalkD
import LeanVM.Guest.B1.VsC.Os.LeftPre
import LeanVM.Guest.B1.VsC.Os.WalkArms
import LeanVM.Guest.B1.VsC.Os.LeftBody
import LeanVM.Guest.B1.VsC.Os.LeftHeap
import LeanVM.Guest.B1.VsC.Os.LeftNode
import LeanVM.Guest.B1.VsC.Os.KindsA
import LeanVM.Guest.B1.VsC.Os.LeftOs
import LeanVM.Guest.B1.VsC.Os.IsZeroA
import LeanVM.Guest.B1.VsC.Os.LeftCalls
import LeanVM.Guest.B1.VsC.Os.LeftLq
import LeanVM.Guest.B1.VsC.Os.LeftLqMem

/-!
# `open_stacked`'s pieces, pinned

`level_queries` at any second argument (`LqAG`, every `lqTable` entry), the body's honest data
after Hotwire's finish (`os_honest_proved`), and the walk of a flat body with dispatches. On Lean's
three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.lqAG_complete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqAG_complete'

/-- info: 'LeanVM.Guest.B1.VsC.lqAG_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqAG_all

/-- info: 'LeanVM.Guest.B1.Whir.osFinishA_completeC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osFinishA_completeC

/-- info: 'LeanVM.Guest.B1.Whir.body_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.body_of

/-- info: 'LeanVM.Guest.B1.Whir.os_honest_proved' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.os_honest_proved

/-- info: 'LeanVM.Guest.B1.walk_flatD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.walk_flatD

/-- info: 'LeanVM.Guest.B1.selOk_of_allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.selOk_of_allOk

/-- info: 'LeanVM.Guest.B1.fdEvs_holds_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.fdEvs_holds_all

/-- info: 'LeanVM.Guest.B1.VsC.osHonest_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osHonest_of_open

/-- info: 'LeanVM.Guest.B1.Whir.osBody_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osBody_walk

/-- info: 'LeanVM.Guest.B1.Whir.osBody_evs_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osBody_evs_congr

/-- info: 'LeanVM.Guest.B1.Whir.osArm_walk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osArm_walk

/-- info: 'LeanVM.Guest.B1.Whir.callsAgree_flatD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.callsAgree_flatD

/-- info: 'LeanVM.Guest.B1.flatD_parts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.flatD_parts

/-- info: 'LeanVM.Guest.B1.Whir.osArm_nodeAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osArm_nodeAt

/-- info: 'LeanVM.Guest.B1.loadAddrs_flatD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.loadAddrs_flatD

/-- info: 'LeanVM.Guest.B1.heapHintAddrs_flatD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.heapHintAddrs_flatD

/-- info: 'LeanVM.Guest.B1.noHeap_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.noHeap_all

/-- info: 'LeanVM.Guest.B1.VsC.osHonestA_valC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osHonestA_valC

/-- info: 'LeanVM.Guest.B1.VsC.osWords_in' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osWords_in

/-- info: 'LeanVM.Guest.B1.VsC.osWords_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osWords_mem

/-- info: 'LeanVM.Guest.B1.VsC.osLoads_cells' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osLoads_cells

/-- info: 'LeanVM.Guest.B1.VsC.os_fn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.os_fn

/-- info: 'LeanVM.Guest.B1.VsC.osCallAtA_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osCallAtA_of_kids

/-- info: 'LeanVM.Guest.B1.VsC.openStackedCompleteA_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openStackedCompleteA_of_kids

/-- info: 'LeanVM.Guest.B1.VsC.osLeftC_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osLeftC_of_kids

/-- info: 'LeanVM.Guest.B1.VsC.opening_message_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.opening_message_leafA

/-- info: 'LeanVM.Guest.B1.VsC.fold_final_msg_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.fold_final_msg_leafA

/-- info: 'LeanVM.Guest.B1.VsC.opening_tail_round_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.opening_tail_round_leafA

/-- info: 'LeanVM.Guest.B1.VsC.osHonest_of_openOs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osHonest_of_openOs

/-- info: 'LeanVM.Guest.B1.VsC.is_zero_leafA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.is_zero_leafA

/-- info: 'LeanVM.Guest.B1.VsC.osBody_calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osBody_calls

/-- info: 'LeanVM.Guest.B1.Whir.LvsAtRun.phase_idx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.LvsAtRun.phase_idx

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.qs_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.qs_os

/-- info: 'LeanVM.Guest.B1.Whir.osCapDepth_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.osCapDepth_eq

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.capDepthOf_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.capDepthOf_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqCapOk_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqCapOk_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqStatic_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqStatic_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqPops_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqPops_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqOk_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqOk_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.phase_len_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.phase_len_os

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqAt_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqAt_os

/-- info: 'LeanVM.Guest.B1.Whir.oqChain_congr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.oqChain_congr

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqMret_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqMret_os

/-- info: 'LeanVM.Guest.B1.VsC.osHonRun_of_open' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osHonRun_of_open

/-- info: 'LeanVM.Guest.B1.VsC.lqWin_of_runs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqWin_of_runs

/-- info: 'LeanVM.Guest.B1.VsC.osPos_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osPos_le

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.lqPos_os' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.lqPos_os
