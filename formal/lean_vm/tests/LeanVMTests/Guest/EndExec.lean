import LeanVM.Guest.EndExecRuns
import LeanVM.Guest.EndExecRoute
import LeanVM.Guest.EndExecCoreA
import LeanVM.Guest.CoreMode.Fam.EntA
import LeanVM.Guest.EndExecCoreGhost
import LeanVM.Guest.EndExecCoreGhostD

/-!
# The executor along a reference run, pinned

The core route's chain (`execute_ref`, from `ExecGaps` and a reference run), the trace and the
reference's part of each step, on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.EndExec.execute_ref' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.execute_ref

/-- info: 'LeanVM.Guest.EndExec.refOk_of_trace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.refOk_of_trace

/-- info: 'LeanVM.Guest.Mode.guest_decodable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.guest_decodable

/-- info: 'LeanVM.Guest.Mode.guest_windows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.guest_windows

/-- info: 'LeanVM.Guest.EndExec.usedNextAll_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.usedNextAll_of

/-- info: 'LeanVM.Guest.EndExec.ExecGaps.ofRoute' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ExecGaps.ofRoute

/-- info: 'LeanVM.Guest.EndExec.resRef_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.resRef_of_sub

/-- info: 'LeanVM.Guest.EndExec.termRef_of_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.termRef_of_sub

/-- info: 'LeanVM.Guest.EndExec.entIdx_alignA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.entIdx_alignA

/-- info: 'LeanVM.Guest.Bridge.RefOk.framesA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.RefOk.framesA

/-- info: 'LeanVM.Guest.Bridge.insts_main_orA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.insts_main_orA

/-- info: 'LeanVM.Guest.Bridge.jumpF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.jumpF_of

/-- info: 'LeanVM.Guest.Bridge.tailF_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Bridge.tailF_of

/-- info: 'LeanVM.Guest.EndExec.kid_retsA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.kid_retsA

/-- info: 'LeanVM.Guest.EndExec.honB_track' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.honB_track

/-- info: 'LeanVM.Guest.EndExec.coreHonAll_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.coreHonAll_A

/-- info: 'LeanVM.Guest.Res.insts_downA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Res.insts_downA

/-- info: 'LeanVM.Guest.EndExec.insts_allA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.insts_allA

/-- info: 'LeanVM.Guest.EndExec.inst_frameA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.inst_frameA

/-- info: 'LeanVM.Guest.EndExec.resOk_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.resOk_instA

/-- info: 'LeanVM.Guest.EndExec.resOk_instGA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.resOk_instGA

/-- info: 'LeanVM.Guest.EndExec.gwAlias_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.gwAlias_instA

/-- info: 'LeanVM.Guest.EndExec.dimFacts_okW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.dimFacts_okW

/-- info: 'LeanVM.Guest.EndExec.expFacts_okW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.expFacts_okW

/-- info: 'LeanVM.Guest.EndExec.vs_cst' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.vs_cst

/-- info: 'LeanVM.Guest.EndExec.ghostOk_guest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.ghostOk_guest

/-- info: 'LeanVM.Guest.EndExec.linkQ_allA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.linkQ_allA

/-- info: 'LeanVM.Guest.EndExec.glF_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.glF_instA

/-- info: 'LeanVM.Guest.EndExec.alGlF_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.alGlF_instA

/-- info: 'LeanVM.Guest.EndExec.st_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.st_instA

/-- info: 'LeanVM.Guest.EndExec.coreGhost_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.coreGhost_of

/-- info: 'LeanVM.Guest.EndExec.coreHonAll_ghost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.coreHonAll_ghost
