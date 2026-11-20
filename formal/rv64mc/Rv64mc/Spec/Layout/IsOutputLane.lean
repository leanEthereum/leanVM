/-
  Rv64mc.Spec.Layout.IsOutputLane

  The contract of `verifier::layout::is_output_lane(column: usize) -> bool`: `column` in `a0`, the result
  `Model.isOutputLaneRust` in `a0`.
-/

import Rv64mc.Spec.Layout.Basic
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout.IsOutputLane

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A leaf without a frame. -/
def need : Nat := 0

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = ofBool (Model.isOutputLaneRust (regs .x10).toNat)

/-- **The contract of `is_output_lane`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Layout.IsOutputLane
