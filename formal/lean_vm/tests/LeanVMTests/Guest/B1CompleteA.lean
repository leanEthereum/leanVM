import LeanVM.Guest.Complete.MainA
import LeanVM.Guest.Complete.PureA
import LeanVM.Guest.Complete.LeafA
import LeanVM.Guest.Complete.DigestA
import LeanVM.Guest.Complete.StraightA
import LeanVM.Guest.Complete.DaPadA
import LeanVM.Guest.Complete.KidsA
import LeanVM.Guest.Complete.MainCalleesA
import LeanVM.Guest.Complete.MainEval
import LeanVM.Guest.Complete.MainSeg
import LeanVM.Guest.Complete.DupA
import LeanVM.Guest.Complete.MainDup
import LeanVM.Guest.Complete.MainWin

/-!
# `main`'s placed completeness, pinned

`verify_sub`'s placed completeness as a fresh callee (`VsCompleteHypA.at`) and the pieces of
`main`'s placed completeness, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.Complete.VsCompleteHypA.at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.VsCompleteHypA.at

/-- info: 'LeanVM.Guest.Complete.loadsR_hintsR_of_loadOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loadsR_hintsR_of_loadOk

/-- info: 'LeanVM.Guest.Complete.callCompletesA_of_loadOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callCompletesA_of_loadOk

/-- info: 'LeanVM.Guest.Complete.callAtA_leafBuf' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_leafBuf

/-- info: 'LeanVM.Guest.Complete.exponent_tables_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.exponent_tables_callAtA

/-- info: 'LeanVM.Guest.Complete.statement_digest_callCompletesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.statement_digest_callCompletesA

/-- info: 'LeanVM.Guest.Complete.callAtA_straight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_straight

/-- info: 'LeanVM.Guest.Complete.callAtA_straightL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_straightL

/-- info: 'LeanVM.Guest.Complete.padL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.padL_callAtA

/-- info: 'LeanVM.Guest.Complete.da_pad_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_pad_callAtA

/-- info: 'LeanVM.Guest.Complete.da_padding_callCompletesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.da_padding_callCompletesA

/-- info: 'LeanVM.Guest.Complete.loadsR_hintsR_of_leafPlain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.loadsR_hintsR_of_leafPlain

/-- info: 'LeanVM.Guest.Complete.statement_digest_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.statement_digest_callAtA

/-- info: 'LeanVM.Guest.Complete.kid_step' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kid_step

/-- info: 'LeanVM.Guest.Complete.kidL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.kidL_callAtA

/-- info: 'LeanVM.Guest.Complete.mVal_goodPre' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_goodPre

/-- info: 'LeanVM.Guest.Complete.mVal_goodDa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_goodDa

/-- info: 'LeanVM.Guest.Complete.mVal_goodAgg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_goodAgg

/-- info: 'LeanVM.Guest.Complete.mVal_goodPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mVal_goodPost

/-- info: 'LeanVM.Guest.Complete.segA_callIfT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_callIfT

/-- info: 'LeanVM.Guest.Complete.segA_callIfN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.segA_callIfN

/-- info: 'LeanVM.Guest.Complete.holdsT_plain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsT_plain

/-- info: 'LeanVM.Guest.Complete.holdsT_rc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsT_rc

/-- info: 'LeanVM.Guest.Complete.holdsT_touch' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsT_touch

/-- info: 'LeanVM.Guest.Complete.holdsT_load' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsT_load

/-- info: 'LeanVM.Guest.Complete.holdsT_store' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.holdsT_store

/-- info: 'LeanVM.Guest.Complete.dupL_callAtA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dupL_callAtA

/-- info: 'LeanVM.Guest.Complete.dupHyps0_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dupHyps0_static

/-- info: 'LeanVM.Guest.Complete.dupHyps1_static' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dupHyps1_static

/-- info: 'LeanVM.Guest.Complete.coveragePlan_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.coveragePlan_eq

/-- info: 'LeanVM.Guest.Complete.dup_atEvery' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dup_atEvery

/-- info: 'LeanVM.Guest.Complete.mainDupx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainDupx

/-- info: 'LeanVM.Guest.Complete.mainDups' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainDups

/-- info: 'LeanVM.Guest.Complete.dups_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.dups_lt

/-- info: 'LeanVM.Guest.Complete.MainCalleesOpenA.toMainCalleesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.MainCalleesOpenA.toMainCalleesA

/-- info: 'LeanVM.Guest.Complete.callAtA_main_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.callAtA_main_of_window

/-- info: 'LeanVM.Guest.Complete.mainCompleteA_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCompleteA_of_window

/-- info: 'LeanVM.Guest.Complete.mainCalleesA_to_mainFromVs_of_window' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Complete.mainCalleesA_to_mainFromVs_of_window
