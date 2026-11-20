/-
  Rv64mc.Spec.Bytecode.Evaluate

  The contract of `Bytecode::evaluate(&self, point: &[E]) -> Result<E, VerifierError>`: the result's slot (`sret`)
  in `a0`, the bytecode in `a1` (`Walk.BytecodeAt`), the point as a slice (`a2`, `a3`, its elements live). It writes
  `Model.evaluateRust`'s answer at `sret` (`ResultEAt`): `Ok` with the value, or `Err(MultilinearSize)` where the
  point's size does not match.
-/

import Rv64mc.Spec.Walk.Repr
import Rv64mc.Spec.Whir.Basic
import Rv64mc.Model.Bytecode

namespace Rv64mc.Spec.Bytecode.Evaluate

open RiscvZkvm.Rv64 Lprog Lprog.RiscV LeanVM.Parameters Rv64mc.Spec.Transcript

def Pre (env : Env) (bc : Model.BytecodeRust) (pt : List E) (regs : Reg → Word) (m : MachineState) : Prop :=
  InFrame (regs .x2) (regs .x10) Layouts.ResultE.byteSize ∧
    env.Owned m (regs .x2) (regs .x11) Layouts.Bytecode.byteSize ∧ Walk.BytecodeAt env m (regs .x11) bc ∧
    SliceArgs EListAt m (regs .x12) (regs .x13) (pt.map Model.limbs) ∧
    env.Live m (regs .x12) (Layouts.E.byteSize * pt.length)

def Post (bc : Model.BytecodeRust) (pt : List E) (regs : Reg → Word) (_m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  ResultEAt m' (regs .x10) (Model.evaluateRust bc pt)

/-- **The contract of `Bytecode::evaluate`**, function `i` of `p` with `need` bytes of stack (its frame is 160
    bytes; it calls `eq_kernel` twice and the blocks' weighted sum), for every bytecode and point. -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  ∀ bc pt, Holds env p i need (Pre env bc pt) (Post bc pt) (Whir.SretOut Layouts.ResultE.byteSize)

end Rv64mc.Spec.Bytecode.Evaluate
