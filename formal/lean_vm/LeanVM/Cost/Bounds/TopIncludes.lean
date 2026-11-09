module

public import LeanVM.Cost.Bounds.Basic
public import LeanVM.Cost.Extractor.Top

/-!
# Bounds: the programs' inclusions between the extractor's top functions

`includes` on the top functions' lists of about `500` bodies (a membership proof per body) takes
seconds each, so each is a lemma of its own, here, apart from the bounds that use them
(`Bounds/Top.lean`): they build while the bounds `Top` imports do, and an edit of `Top` rebuilds
none of them.
-/

namespace LeanVM.Cost.Bounds

open LeanVM.Cost LeanVM.Cost.Extractor LeanVM.Cost.Library

public section

variable (P : LeanVM.Cost.MachineProgram)

set_option maxHeartbeats 1000000 in
theorem includes_stageTC (hP : Includes P afterRootStageC.costDeps) : Includes P stageTC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootStageLam (hP : Includes P afterRootStageC.costDeps) :
    Includes P afterRootStageC.lam0.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootStageC (hP : Includes P extractorC.costDeps) :
    Includes P afterRootStageC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_extractorLam (hP : Includes P extractorC.costDeps) :
    Includes P extractorC.lam0.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_afterRootLiteC (hP : Includes P extractorC.costDeps) :
    Includes P afterRootLiteC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_bytecodeWordsC (hP : Includes P extractorC.costDeps) :
    Includes P bytecodeWordsC.costDeps := by
  includes

set_option maxHeartbeats 1000000 in
theorem includes_bindC (hP : Includes P extractorC.costDeps) :
    Includes P Auto.Option.bind.c154.costDeps := by
  includes

end

end LeanVM.Cost.Bounds
