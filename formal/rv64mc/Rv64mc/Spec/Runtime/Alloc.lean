/-
  Rv64mc.Spec.Runtime.Alloc

  The contract of the bump allocator's `GlobalAlloc::alloc` (`guest/src/main.rs`): called with a `Layout`, its
  alignment in `a0` and its size in `a1` (`Layouts.AllocLayout`: `align` first), it returns in `a0` the first
  multiple of the alignment at or above `NEXT`, and moves `NEXT` to the end of the block, within the heap; out of
  heap it halts (`halt(2)`), which the contract, partial, leaves out. So the block is `Fresh`: apart from everything
  allocated before it.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- `alloc`'s precondition: a nonzero alignment below `2^63` (a `Layout`'s is a power of two at most `2^62`). -/
def AllocPre (regs : Reg → Word) (_m : MachineState) : Prop :=
  0 < (regs .x10).toNat ∧ (regs .x10).toNat < 2 ^ 63

/-- `alloc`'s postcondition: the block `[a0, a0 + size)` starts at an aligned address at or above `NEXT`, and ends
    at the new `NEXT`. -/
def AllocPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  (env.next m).toNat ≤ (r' .x10).toNat ∧ (r' .x10).toNat % (regs .x10).toNat = 0 ∧
    (r' .x10).toNat + (regs .x11).toNat = (env.next m').toNat

/-- **The contract of `alloc`.** -/
def AllocSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need AllocPre (AllocPost env)

/-- What `alloc` returns is `Fresh`. -/
theorem AllocPost.fresh {env : Env} {regs r' : Reg → Word} {m m' : MachineState}
    (h : AllocPost env regs m r' m') : env.Fresh m m' (r' .x10) (regs .x11).toNat :=
  ⟨h.1, Nat.le_of_eq h.2.2⟩

end Rv64mc.Spec.Runtime
