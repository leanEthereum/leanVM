import LeanVM.Guest.B1.VsC.Os.LeftEnd

/-!
# `open_stacked`'s end, bounded, pinned

vsc33: every callee's end bounded by its sizes and frames, each level's and the tail's, so `OpenStackedEndA` at every arm when every compiled frame is at most `2^16`. On Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.B1.VsC.lpAE_b2c' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lpAE_b2c

/-- info: 'LeanVM.Guest.B1.VsC.oqAE_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.oqAE_all

/-- info: 'LeanVM.Guest.B1.VsC.lqAGE_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lqAGE_all

/-- info: 'LeanVM.Guest.B1.VsC.lrAE_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrAE_complete

/-- info: 'LeanVM.Guest.B1.VsC.lrsAE_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.lrsAE_complete

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.osChainB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.osChainB

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.kidsAtF_tailB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.kidsAtF_tailB

/-- info: 'LeanVM.Guest.B1.VsC.osBnd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osBnd

/-- info: 'LeanVM.Guest.B1.Whir.HonRun.osKidsAt_of_post' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.Whir.HonRun.osKidsAt_of_post

/-- info: 'LeanVM.Guest.B1.VsC.osCallAtA_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osCallAtA_of_kids

/-- info: 'LeanVM.Guest.B1.VsC.openStackedEndA_of_kids' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openStackedEndA_of_kids

/-- info: 'LeanVM.Guest.B1.VsC.openStackedEndA_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openStackedEndA_all

/-- info: 'LeanVM.Guest.B1.VsC.openStackedEndA_17' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.openStackedEndA_17

/-- info: 'LeanVM.Guest.B1.VsC.osFs_le16' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.osFs_le16
