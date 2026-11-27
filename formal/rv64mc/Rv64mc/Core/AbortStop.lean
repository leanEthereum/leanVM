/-
  Rv64mc.Core.AbortStop

  The stopping set the total contracts of the functions `main` reaches share: the run ends at the halting `ECALL`
  with `a0 = 2`, the guest's abort code (a panic, the allocator out of heap, an input that does not decode). `main`'s
  `MainStopT` (`Final/MainSpecT.lean`) is this set, so a callee's stop is a stop of `main`'s without a weakening.
  A finer stop (`AllocStop`) is weakened to it by `HoldsT.mono_stop`.

  ## Main definitions

  * `AbortStop`
-/

import Rv64mc.Core.HoldsT

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The guest's abort**: the run ends with `a0 = 2`. -/
def AbortStop (_regs : Reg → Word) (_m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = 2

end Rv64mc
