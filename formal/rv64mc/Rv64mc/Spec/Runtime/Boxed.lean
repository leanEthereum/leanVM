/-
  Rv64mc.Spec.Runtime.Boxed

  The contract of `Box::<T>::new_uninit` as the image has it (one instance, `T` of `size` bytes, its size a constant
  of the code): a fresh 8-aligned block of `size` bytes in `a0`; out of heap it halts.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- **The contract of `Box::<T>::new_uninit`**, `T` of `size` bytes. -/
def BoxNewUninitSpec (env : Env) (size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun _ _ => True)
    (fun _ m r' m' => (r' .x10).toNat % 8 = 0 ∧ env.Fresh m m' (r' .x10) size)

end Rv64mc.Spec.Runtime
