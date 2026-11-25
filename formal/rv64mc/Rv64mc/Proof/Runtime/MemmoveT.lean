/-
  Rv64mc.Proof.Runtime.MemmoveT

  The total contract of `compiler_builtins`' `memmove(dst, src, n)` (`MemmoveSpecT`).

  ## Main definitions

  * `MemmoveSpecT`
-/

import Rv64mc.Spec.Runtime.MemT

namespace Rv64mc.Proof.Runtime.MemmoveT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime

/-- **The total contract of `memmove`**: from `CopyPreT true` (the ranges may overlap), it returns `dst` with
    `[dst, dst + n)` holding what `[src, src + n)` held, writing at most the doublewords of the destination besides
    its stack (`CopyOut`). -/
def MemmoveSpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CopyPreT true env) (CopyPostT env) CopyOut

end Rv64mc.Proof.Runtime.MemmoveT
