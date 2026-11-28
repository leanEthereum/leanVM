import LeanVM.Guest.B1.VsC.CstWalk
import LeanVM.Guest.B1.VsC.CstWords
import LeanVM.Guest.B1.VsC.CstWordsIn
import LeanVM.Guest.B1.VsC.CstA

/-! `check_stack_terminal`'s completeness pieces, pinned at Lean's three axioms. -/

/-- info: 'LeanVM.Guest.B1.VsC.cst_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cst_value

/-- info: 'LeanVM.Guest.B1.VsC.walk_cst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.walk_cst

/-- info: 'LeanVM.Guest.B1.VsC.cst_chk' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cst_chk

/-- info: 'LeanVM.Guest.B1.VsC.cst_wordsInA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cst_wordsInA

/-- info: 'LeanVM.Guest.B1.VsC.CstHyp.holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CstHyp.holds

/-- info: 'LeanVM.Guest.B1.VsC.CstHyp.allOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CstHyp.allOk

/-- info: 'LeanVM.Guest.B1.VsC.CstHyp.assert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CstHyp.assert

/-- info: 'LeanVM.Guest.B1.VsC.CstG.calls' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.CstG.calls

/-- info: 'LeanVM.Guest.B1.VsC.cst_completeA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.B1.VsC.cst_completeA
