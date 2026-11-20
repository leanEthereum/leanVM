/-
  Rv64mc.Core.Abi

  The calling convention's part of every contract: the registers a function keeps, what a postcondition says of
  them, of the stack pointer and of the memory above it, and the entry a precondition assumes.
-/

import LprogRiscV.Lsym

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The registers a function keeps (`s0`..`s11`). -/
def Saved : List Reg := [.x8, .x9, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- **The ABI's part of a postcondition**: the stack pointer back at `top`, the saved registers kept, and the memory
    from `top` up kept. -/
def Abi (top : Word) (regs r' : Reg → Word) (m m' : MachineState) : Prop :=
  r' .x2 = top ∧ r' .x8 = regs .x8 ∧ r' .x9 = regs .x9 ∧ r' .x18 = regs .x18 ∧ r' .x19 = regs .x19 ∧
    r' .x20 = regs .x20 ∧ r' .x21 = regs .x21 ∧ r' .x22 = regs .x22 ∧ r' .x23 = regs .x23 ∧
    r' .x24 = regs .x24 ∧ r' .x25 = regs .x25 ∧ r' .x26 = regs .x26 ∧ r' .x27 = regs .x27 ∧
    ∀ a, top ≤ a → m'.getMem a = m.getMem a

/-- The precondition every contract has: called from `ret`, with the stack at `top`. -/
def Entry (ret top : Word) (regs : Reg → Word) : Prop := regs .x1 = ret ∧ regs .x2 = top

end Rv64mc
