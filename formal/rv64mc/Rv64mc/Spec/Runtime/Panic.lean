/-
  Rv64mc.Spec.Runtime.Panic

  The contract of the functions that never return: `verifier_rv64::halt` (which halts with `a0 = 2`, a verdict
  that is not acceptance), the panic handler `rust_begin_unwind` that calls it, and every panic entry of `core` and
  `alloc` the image keeps, each a call of the next (`panic = "abort"`: a panic is the handler).
-/

import Rv64mc.Core.Holds

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **Function `i` of `p` never returns**, from any arguments: its postcondition is `False`, so every run of it
    halts without accepting, traps, or does not end. -/
def NoReturn (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) (fun _ _ _ _ => False)

end Rv64mc.Spec.Runtime
