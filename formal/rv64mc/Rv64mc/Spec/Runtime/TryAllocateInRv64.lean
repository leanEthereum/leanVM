/-
  Rv64mc.Spec.Runtime.TryAllocateInRv64

  The contract of the guest crate's instance of `RawVecInner::try_allocate_in` (`main`'s, `Gen.Idx` module
  `Alloc.RawVec.RawVecInner.TryAllocateInInVerifierRv64`): the uninitialized one, so LLVM drops `init`, and its
  arguments are the result's slot (`a0`), the capacity (`a1`), the element's alignment (`a2`) and size (`a3`), not
  `TryAllocSpec`'s. On `Ok` (tag `0`) the buffer is empty for no bytes (capacity `0`, the dangling pointer the
  alignment, `RawVecInner::new_in`), and otherwise a `Fresh` block of `capacity * size` bytes at a multiple of 8 (the
  bump allocator's). On `Err` it promises nothing (`main` hands the error to `handle_error`, which does not return).
  The result's layout is `TryAllocateIn`'s (`taTagAt`, `taCapAt`, `taPtrAt`).
-/

import Rv64mc.Spec.Runtime.TryAllocateIn

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The precondition: the result slot is the caller's, the alignment and the size a `Layout`'s. -/
def TryAllocRv64Pre (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  env.Owned m (regs .x2) (regs .x10) tryAllocBytes ∧ 0 < (regs .x12).toNat ∧ (regs .x12).toNat ≤ 8 ∧
    0 < (regs .x13).toNat ∧ (regs .x13).toNat < 2 ^ 63

/-- The postcondition: on `Ok`, the bytes asked for fit an `isize`; the buffer is the alignment with capacity `0`
    for no bytes, else a fresh, 8-aligned block with the capacity asked for. -/
def TryAllocRv64Post (env : Env) (regs : Reg → Word) (m : MachineState) (_r' : Reg → Word) (m' : MachineState) :
    Prop :=
  m'.getMem (taTagAt (regs .x10)) = 0#64 →
    (regs .x11).toNat * (regs .x13).toNat < 2 ^ 63 ∧
    (((regs .x11).toNat * (regs .x13).toNat = 0 ∧ m'.getMem (taCapAt (regs .x10)) = 0#64 ∧
        m'.getMem (taPtrAt (regs .x10)) = regs .x12) ∨
      ((regs .x11).toNat * (regs .x13).toNat ≠ 0 ∧ m'.getMem (taCapAt (regs .x10)) = regs .x11 ∧
        env.Fresh m m' (m'.getMem (taPtrAt (regs .x10))) ((regs .x11).toNat * (regs .x13).toNat) ∧
        (m'.getMem (taPtrAt (regs .x10))).toNat % 8 = 0))

/-- **The contract of the guest's `try_allocate_in`.** It writes its result (`TryAllocOut`). -/
def TryAllocRv64Spec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (TryAllocRv64Pre env) (TryAllocRv64Post env) TryAllocOut

end Rv64mc.Spec.Runtime
