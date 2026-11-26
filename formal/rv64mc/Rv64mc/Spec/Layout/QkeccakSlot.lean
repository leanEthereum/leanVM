/-
  Rv64mc.Spec.Layout.QkeccakSlot

  The contract of `verifier::layout::qkeccak_slot(column: usize) -> Option<usize>`: `column` in `a0`, the result
  `Model.qkeccakSlotRust` returned as an `Option<usize>` in `a0`, `a1` (`OptUsizeRet`).
-/

import Rv64mc.Spec.Layout.Basic
import Rv64mc.Model.Layout

namespace Rv64mc.Spec.Layout.QkeccakSlot

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A leaf without a frame. -/
def need : Nat := 0

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  OptUsizeRet r' (Model.qkeccakSlotRust (regs .x10).toNat)

/-- **The contract of `qkeccak_slot`**, function `i` of `p`. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Layout.QkeccakSlot
