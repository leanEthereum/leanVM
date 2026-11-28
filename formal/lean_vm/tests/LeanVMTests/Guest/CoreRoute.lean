import LeanVM.Guest.EndExecFrame
import LeanVM.Guest.CoreMode.HeapCTree
import LeanVM.Guest.CoreMode.CoreLoopC
import LeanVM.Guest.EndExecCoreSplit

/-!
# The core route's generic theorems, pinned

A function whose core data the route's checks accept meets its frame interface (`frameSpec_core`, a
loop helper's `frameSpec_loopC`), the heap check's soundness over an honest call tree
(`heapOkC_sound`), and `ExecGaps.frame` from every function's (`frame_core`), on Lean's three axioms.
-/

/-- info: 'LeanVM.Guest.CoreMode.frameSpec_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.frameSpec_core

/-- info: 'LeanVM.Guest.CoreMode.frameSpec_loopC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.frameSpec_loopC

/-- info: 'LeanVM.Guest.CoreMode.heapOkC_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.heapOkC_sound

/-- info: 'LeanVM.Guest.Mode.fnSpecC_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.Mode.fnSpecC_of

/-- info: 'LeanVM.Guest.EndExec.frame_core' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.frame_core

/-- info: 'LeanVM.Guest.CoreMode.fnSpecC_of_loopC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.fnSpecC_of_loopC

/-! A needed run with a constant lower bound and an upper bound a fact bounds (`ptsU`, `runOk1P`'s case): its cells
from the lower bound to the fact's bound each witnessed (`pt`), sound by `runOk1P_ok`. -/

open LeanVM.Guest.CoreMode in
example (pt : CCell → Wit → Bool) (X : CX) (st : CSt) (Q : PRun) (n : ℕ) (res : List ℕ) (ws : List Wit) :
    runOk1P pt X st Q (.ptsU n res :: ws) =
      bif Q.lo.bases.isEmpty && Nat.blt Q.lo.off capE && hasFU (facts X st.env res) Q.hi (n + 1)
      then ptsRunP pt Q.base Q.stride Q.lo.off (n - Q.lo.off) ws else none := rfl

/-- info: 'LeanVM.Guest.CoreMode.runOk1P_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.runOk1P_ok

/-! A split's arm checked under its selector's value (`armPath`, `heapOkC1P`), where every returning path reaches a
selection on it (`selReach`); a split's count below `S·A` (`splitRes`). -/

open LeanVM.Guest.CoreMode in
example (x r : ℕ) (body : List LeanVM.Guest.Core.Stmt) :
    armPath x r body = bif selReach x body then [.arm x r] else [] := rfl

/-- info: 'LeanVM.Guest.CoreMode.selReach_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.selReach_sound

/-- info: 'LeanVM.Guest.CoreMode.armPath_holds' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.CoreMode.armPath_holds

/-- info: 'LeanVM.Guest.EndExec.splitRes_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms LeanVM.Guest.EndExec.splitRes_sound
