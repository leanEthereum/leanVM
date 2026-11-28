import LeanVM.Guest.Memory.GuestWordsA
import LeanVM.Guest.Budget.Shape
import LeanVM.Guest.Budget.Words
import LeanVM.Guest.Memory.GuestWordsH
import LeanVM.Guest.Memory.StaticShift
import LeanVM.Guest.Budget.HandCount

/-!
# The guest's words on the aligned allocator, pinned

The aligned words within the static checker's cost, the guest's certificates checked by the kernel, and a
child's shape off its proof, on Lean's three axioms (a subset of them).
-/

/-- info: 'LeanVM.Guest.Memory.wordsA_le_total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wordsA_le_total

/-- info: 'LeanVM.Guest.Memory.wordsA_le_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wordsA_le_cost

/-- info: 'LeanVM.Guest.Memory.wa_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wa_checked

/-- info: 'LeanVM.Guest.Memory.wa_cost_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wa_cost_le_of_stat

/-- info: 'LeanVM.Guest.Memory.wa_cost_le_of_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wa_cost_le_of_loop

/-- info: 'LeanVM.Guest.Memory.wa_wordsA_le_of_stat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wa_wordsA_le_of_stat

/-- info: 'LeanVM.Guest.Budget.shapeOf_admissible_of_rel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.shapeOf_admissible_of_rel


/-- info: 'LeanVM.Guest.Budget.wordsA_le_of_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.wordsA_le_of_cost

/-- info: 'LeanVM.Guest.Budget.logMem_wordsA_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.logMem_wordsA_le

/-- info: 'LeanVM.Guest.Memory.chk_soundH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.chk_soundH

/-- info: 'LeanVM.Guest.Memory.cost_le_of_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.cost_le_of_hand

/-- info: 'LeanVM.Guest.Memory.checkedH_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.checkedH_of

/-- info: 'LeanVM.Guest.Budget.wa_checkedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.wa_checkedH

/-- info: 'LeanVM.Guest.Budget.mainCostWithin_of_hand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.mainCostWithin_of_hand

/-- info: 'LeanVM.Guest.Memory.wh_checkedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wh_checkedH

/-- info: 'LeanVM.Guest.Memory.wz_checkedH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wz_checkedH

/-- info: 'LeanVM.Guest.Memory.wh_loopChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wh_loopChecked

/-- info: 'LeanVM.Guest.Memory.wz_loopChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wz_loopChecked

/-- info: 'LeanVM.Guest.Memory.checkedH_of_chkHJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.checkedH_of_chkHJ

/-- info: 'LeanVM.Guest.Memory.statB_shift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.statB_shift

/-- info: 'LeanVM.Guest.Memory.loopRun_cost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.loopRun_cost_le

/-- info: 'LeanVM.Guest.Memory.checkedH_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.checkedH_at

/-- info: 'LeanVM.Guest.Memory.mainCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.mainCost_le

/-- info: 'LeanVM.Guest.Memory.wh_nodeIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wh_nodeIdx

/-- info: 'LeanVM.Guest.Memory.wz_nodeIdx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wz_nodeIdx

/-- info: 'LeanVM.Guest.Memory.wh_checkedH_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wh_checkedH_at

/-- info: 'LeanVM.Guest.Memory.wz_checkedH_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wz_checkedH_at

/-- info: 'LeanVM.Guest.Memory.wh_mainCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wh_mainCost_le

/-- info: 'LeanVM.Guest.Memory.wz_mainCost_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Memory.wz_mainCost_le

/-- info: 'LeanVM.Guest.Budget.nodeWordsC_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.nodeWordsC_le

/-- info: 'LeanVM.Guest.Budget.logMem_le_of_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.logMem_le_of_count

/-- info: 'LeanVM.Guest.Budget.wh_cost_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.wh_cost_le_count

/-- info: 'LeanVM.Guest.Budget.wz_cost_le_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Budget.wz_cost_le_count
