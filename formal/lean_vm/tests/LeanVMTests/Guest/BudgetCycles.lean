import LeanVM.Guest.Budget.CheckerCount

/-!
# The guest's instruction counts by opcode, pinned

The vector families with hand functions, the counts as weights, the guest's families checked by the
kernel, `main`'s instructions within the checker's count, and the steps and committed size from the
budget, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Memory.chkHJV_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHJV_proj

/-- info: 'LeanVM.Guest.Memory.rangeOk_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.rangeOk_proj

/-- info: 'LeanVM.Guest.Memory.chkHandV_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHandV_proj

/-- info: 'LeanVM.Guest.Memory.chkHandLV_proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHandLV_proj

/-- info: 'LeanVM.Guest.Memory.chkHJV_of_hand_run' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHJV_of_hand_run

/-- info: 'LeanVM.Guest.Memory.chkHJV_of_hand_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHJV_of_hand_split

/-- info: 'LeanVM.Guest.Memory.chkHJV_of_loop_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chkHJV_of_loop_run

/-- info: 'LeanVM.Guest.Memory.loopRun_cost_leA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.loopRun_cost_leA

/-- info: 'LeanVM.Guest.Memory.mainCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.mainCost_le

/-- info: 'LeanVM.Guest.Memory.NodeIdxV.proj' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.NodeIdxV.proj

/-- info: 'LeanVM.Guest.Memory.mainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.mainWeight_le

/-- info: 'LeanVM.Guest.B2C.cnt_le_weight_arm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B2C.cnt_le_weight_arm

/-- info: 'LeanVM.Guest.B2C.xmssArmC_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B2C.xmssArmC_spec

/-- info: 'LeanVM.Guest.Memory.cntOm_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.cntOm_eq

/-- info: 'LeanVM.Guest.Memory.ch_checkedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.ch_checkedH

/-- info: 'LeanVM.Guest.Memory.cz_checkedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.cz_checkedH

/-- info: 'LeanVM.Guest.Memory.ch_nodeIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.ch_nodeIdx

/-- info: 'LeanVM.Guest.Memory.cz_nodeIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.cz_nodeIdx

/-- info: 'LeanVM.Guest.Memory.ch_mainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.ch_mainWeight_le

/-- info: 'LeanVM.Guest.Memory.cz_mainWeight_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.cz_mainWeight_le

/-- info: 'LeanVM.Guest.Budget.ch_weight_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.ch_weight_le_count

/-- info: 'LeanVM.Guest.Budget.cz_weight_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.cz_weight_le_count

/-- info: 'LeanVM.Guest.Budget.opcodeCount_le_cnt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.opcodeCount_le_cnt

/-- info: 'LeanVM.Guest.Budget.rows_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.rows_le_count

/-- info: 'LeanVM.Guest.Budget.cnt_le_budget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.cnt_le_budget

/-- info: 'LeanVM.Guest.Budget.rowsC_values' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.rowsC_values

/-- info: 'LeanVM.Guest.Budget.cycles_committed_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.cycles_committed_of_count

/-- info: 'LeanVM.Guest.Budget.checker_aboveRows' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checker_aboveRows

/-- info: 'LeanVM.Guest.Budget.checkerZero_aboveRows' does not depend on any axioms -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checkerZero_aboveRows

/-- info: 'LeanVM.Guest.Budget.checker_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checker_bounds

/-- info: 'LeanVM.Guest.Budget.checkerZero_bounds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.checkerZero_bounds
