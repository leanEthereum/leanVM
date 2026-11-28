import LeanVM.Guest.Complete.Claims.CoverRaw

/-!
# The honest coverage table, pinned

`honestCover`: its length, the children's marks (`KidCover`), the raw slots' marks, the slots' bounds.
Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.honestCover_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honestCover_length

/-- info: 'LeanVM.Guest.Complete.kidCover_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidCover_honest

/-- info: 'LeanVM.Guest.Complete.honestCover_rawx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honestCover_rawx

/-- info: 'LeanVM.Guest.Complete.honestCover_raws' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.honestCover_raws

/-- info: 'LeanVM.Guest.Complete.xSlot_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.xSlot_lt

/-- info: 'LeanVM.Guest.Complete.sSlot_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.sSlot_lt

/-- info: 'LeanVM.Guest.Complete.xPlan_directSlots_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.xPlan_directSlots_length

/-- info: 'LeanVM.Guest.Complete.sPlan_directSlots_length' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.sPlan_directSlots_length

/-- info: 'LeanVM.Guest.Complete.rawMarks_honest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.rawMarks_honest
