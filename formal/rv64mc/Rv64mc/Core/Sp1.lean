/-
  Rv64mc.Core.Sp1

  SP1's `ecall` with `t0 = 0` (`HALT`) has no next state: the fact both halting `ecall`s of the image need
  (`_start`'s, `Final/Start.lean`, and `halt`'s, `Proof/Runtime/Halt.lean`).
-/

import LprogRiscV.Sp1Ctx

namespace Rv64mc

open RiscvZkvm.Rv64

/-- SP1's `ecall` with `t0 = 0` (`HALT`) does not continue. -/
theorem sp1Ecall_halt {u : MachineState} (hc : u.code u.pc = some .ECALL) (h5 : u.getReg .x5 = 0) :
    sp1Ecall u = none := by
  have hacc : Sp1.isAccelId 0#64 = false := by decide
  have hhost : Sp1.isHostId 0#64 = true := by decide
  simp [sp1Ecall, hc, h5, hacc, hhost, RiscvZkvm.Rv64.step, Sp1.HINT_LEN, Sp1.HINT_READ, Sp1.COMMIT,
    Sp1.COMMIT_DEFERRED_PROOFS]

end Rv64mc
