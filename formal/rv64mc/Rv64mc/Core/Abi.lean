/-
  Rv64mc.Core.Abi

  The entry every contract's precondition assumes (`Entry`). The registers and memory a call keeps are `Holds`'s
  (`Core/Holds.lean`: `AbiRegs`, `Env.Frame`); the phase-0 probes' `Abi` is in `Probe/Abi.lean`.
-/

import LprogRiscV.Lsym

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The precondition every contract has: called from `ret`, with the stack at `top`. -/
def Entry (ret top : Word) (regs : Reg → Word) : Prop := regs .x1 = ret ∧ regs .x2 = top

end Rv64mc
