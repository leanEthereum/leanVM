/-
  LeanVM.Compiler.Complete.InFrameFn

  `PlaceInFrameStmt`: a scoped function's values are placed in its frame, past the header.
-/

module

public import LeanVM.Compiler.Complete.InFrame
public import LeanVM.Compiler.Complete.ScopedRet
public import LeanVM.Compiler.Complete.Spec

/-!
# P5 for a scoped function

`placeFn_cells` holds on every trace whose return areas fit the return cells, which a scoped
function's do (`scoped_retShort`). `placeFn_ops_inFrame` adds the cells the placed body's
instructions name, which the contract does not state but the frame side uses.
-/

namespace LeanVM.Compiler.Complete

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **P5**: every value of a scoped function placed in a cell is in the frame, past the header. -/
theorem placeFn_inFrame : PlaceInFrameStmt := by
  intro loops sigs t t' tf pf h hs v n hv
  have hc := (placeFn_cells h (scoped_retShort hs)).1
  unfold cellP at hv
  split at hv
  · next c hl =>
    cases hv
    exact hc v _ hl
  · cases hv

/-- Every cell of its own frame an instruction of a scoped function's placed body names is below
the frame size. -/
theorem placeFn_ops_inFrame {loops : Loops} {sigs : SMap (ℕ × ℕ)} {t t' : Tables} {tf : TracedFn}
    {pf : Placed} (h : placeFn loops sigs t tf = .ok (pf, t')) (hs : Scoped tf) :
    OpsBelow pf.fn.frameSize (blockOps pf.fn.body 0) :=
  (placeFn_cells h (scoped_retShort hs)).2

/-- info: 'LeanVM.Compiler.Complete.placeFn_inFrame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms placeFn_inFrame

end
end LeanVM.Compiler.Complete
