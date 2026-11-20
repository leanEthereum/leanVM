/-
  Rv64mc.Spec.Transcript.GrindingBits

  The contract of `verifier::transcript::grinding_bits(numerator: u128) -> u32`: the numerator's low word in `a0`,
  its high word in `a1`; the result in `a0` is `Model.grindingBitsRust`'s. It writes nothing.
-/

import Rv64mc.Core.Holds
import Rv64mc.Model.Transcript

namespace Rv64mc.Spec.Transcript.GrindingBits

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = BitVec.ofNat 64 (Model.grindingBitsRust (regs .x11 ++ regs .x10))

/-- **The contract of `grinding_bits`**, function `i` of `p` with `need` bytes of stack (it has no frame and calls
    nothing). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need (fun _ _ => True) Post

end Rv64mc.Spec.Transcript.GrindingBits
