/-
  Rv64mc.Spec.Bus.BusGrindingBits

  The contract of `verifier::bus::bus_grinding_bits(mu: usize) -> u32`, `grinding_bits(1 << mu)`: `mu` in `a0`, below
  `64` (its one caller requires the push depth below `64` first); the result in `a0` is
  `Model.busGrindingBitsRust`'s. It writes nothing.
-/

import Rv64mc.Core.Holds
import Rv64mc.Model.Bus

namespace Rv64mc.Spec.Bus.BusGrindingBits

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

def Pre (regs : Reg → Word) (_m : MachineState) : Prop := (regs .x10).toNat < 64

def Post (regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = BitVec.ofNat 64 (Model.busGrindingBitsRust (regs .x10).toNat)

/-- **The contract of `bus_grinding_bits`**, function `i` of `p` with `need` bytes of stack (it has no frame and
    tail-calls `grinding_bits`). -/
def spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop := Holds env p i need Pre Post

end Rv64mc.Spec.Bus.BusGrindingBits
