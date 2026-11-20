/-
  Rv64mc.Spec.Runtime.VecReserve

  The contract of `Vec<T>::reserve(&mut self, additional)` (one per `T`, the same code with `T`'s alignment and
  size), on the `Vec` header at `a0` (`Layouts.Vec`): the length is kept; when the spare capacity already holds
  `additional` the header is kept too, and otherwise the buffer grew (`Grown`) to hold `len + additional`. A grow
  that fails does not return (`handle_error`).
-/

import Rv64mc.Spec.Runtime.RawVec

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- `reserve`'s precondition: the header the caller's, its buffer as `grow_amortized` needs it, the length within
    the capacity. -/
def ReservePre (env : Env) (align size : Nat) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) Layouts.Vec.byteSize ∧ GrowPre env align size regs m ∧
    (vecLen m (regs .x10)).toNat ≤ (vecCap m (regs .x10)).toNat

/-- `reserve`'s postcondition. -/
def ReservePost (env : Env) (size : Nat) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word)
    (m' : MachineState) : Prop :=
  vecLen m' (regs .x10) = vecLen m (regs .x10) ∧
    ((regs .x11).toNat ≤ (vecCap m (regs .x10)).toNat - (vecLen m (regs .x10)).toNat →
      vecCap m' (regs .x10) = vecCap m (regs .x10) ∧ vecPtr m' (regs .x10) = vecPtr m (regs .x10)) ∧
    (¬ (regs .x11).toNat ≤ (vecCap m (regs .x10)).toNat - (vecLen m (regs .x10)).toNat →
      Grown env m m' (regs .x10) ((vecLen m (regs .x10)).toNat + (regs .x11).toNat) size)

/-- **The contract of `Vec<T>::reserve`**, `T` of `size` bytes aligned to `align`. -/
def ReserveSpec (env : Env) (align size : Nat) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (ReservePre env align size) (ReservePost env size) GrowOut

end Rv64mc.Spec.Runtime
