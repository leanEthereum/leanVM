/-
  Rv64mc.Proof.Runtime.MemcpyT

  The total contract of `compiler_builtins`' `memcpy(dst, src, n)` (`MemcpySpecT`).

  ## Main definitions

  * `MemcpySpecT`
-/

import Rv64mc.Spec.Runtime.MemT

namespace Rv64mc.Proof.Runtime.MemcpyT

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Rv64mc.Spec.Runtime

/-- **The total contract of `memcpy`**: from `CopyPreT false`, it returns `dst` with `[dst, dst + n)` holding what
    `[src, src + n)` held, writing at most the doublewords of the destination besides its stack (`CopyOut`). -/
def MemcpySpecT (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  HoldsT env p i need (CopyPreT false env) (CopyPostT env) CopyOut

end Rv64mc.Proof.Runtime.MemcpyT
