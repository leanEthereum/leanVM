/-
  Rv64mc.Spec.Runtime.Alloc

  The contract of the bump allocator's `GlobalAlloc::alloc` (`guest/src/main.rs`) as the image has it. The source
  takes a `Layout` and aligns the block to `max(align, 8)`; every caller asks for at most 8, so LLVM drops the
  alignment argument: the size comes in `a0`. It returns in `a0` the first multiple of 8 at or above `NEXT`, and
  moves `NEXT` to the end of the block, within the heap; out of heap it halts (`halt(2)`), which the contract,
  partial, leaves out. So the block is `Fresh`, apart from everything allocated before it, and 8-aligned, so no
  doubleword it shares with an older block starts below it.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- `alloc`'s precondition: a size below `2^63` (a `Layout`'s is at most `isize::MAX`). -/
def AllocPre (regs : Reg → Word) (_m : MachineState) : Prop := (regs .x10).toNat < 2 ^ 63

/-- `alloc`'s postcondition: the block `[a0, a0 + size)` starts at a multiple of 8 at or above `NEXT`, and ends at
    the new `NEXT`. -/
def AllocPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  (env.next m).toNat ≤ (r' .x10).toNat ∧ (r' .x10).toNat % 8 = 0 ∧
    (r' .x10).toNat + (regs .x10).toNat = (env.next m').toNat

/-- **The contract of `alloc`.** -/
def AllocSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need AllocPre (AllocPost env)

/-- What `alloc` returns is `Fresh`. -/
theorem AllocPost.fresh {env : Env} {regs r' : Reg → Word} {m m' : MachineState}
    (h : AllocPost env regs m r' m') : env.Fresh m m' (r' .x10) (regs .x10).toNat :=
  ⟨h.1, Nat.le_of_eq h.2.2⟩

end Rv64mc.Spec.Runtime
