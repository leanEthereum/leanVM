/-
  Rv64mc.Spec.Runtime.MemT

  The total contracts of `compiler_builtins`' `memcpy` and `memmove`: `Mem.lean`'s `CopyPre` and the bytes copied,
  with the windows a total proof needs and a byte frame that leaves out the stack below the stack pointer.

  `CopyPost`'s `ByteFrame` keeps every byte outside the destination, the callee's own stack included. Both functions
  keep scratch in a stack slot (`load_aligned_partial` assembles a partial word there when the source is not 8-byte
  aligned), so it does not hold of their templates. `CopyPostT` keeps every byte outside the destination and outside
  the stack below the stack pointer at entry (`OffStack`), which is all a caller can read afterwards: its objects lie
  at or above its own stack pointer, in the heap, or in the static data.

  The destination lies in a window apart from the static data and `NEXT` (`InWin`), the source in a window
  (`inWindow`: `keccak_f` copies its round constants out of the static data), both apart from the stack below the
  stack pointer, unless there are no bytes (an empty vector's pointer dangles).

  ## Main definitions

  * `InWin`, `OffStack`, `CopyPreT`, `CopyPostT`
-/

import Rv64mc.Spec.Runtime.Mem
import Rv64mc.Core.HoldsT

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The bytes `[a, a + n)` lie below the stack's limit or at or above `sp`: apart from the stack below `sp`. -/
def OffStack (env : Env) (sp a : Word) (n : Nat) : Prop :=
  a.toNat + n ≤ env.stackLimit.toNat ∨ sp.toNat ≤ a.toNat

/-- A copy's total precondition: `CopyPre`, and unless there are no bytes, the destination in the heap window up to
    the heap's end or in the stack window, the source in a window, both apart from the stack below the stack
    pointer. -/
def CopyPreT (overlap : Bool) (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  CopyPre overlap regs m ∧ ((regs .x12).toNat = 0 ∨
    (((0x10000000 ≤ (regs .x10).toNat ∧ (regs .x10).toNat + (regs .x12).toNat ≤ env.heapEnd.toNat) ∨
        (env.stackLimit.toNat ≤ (regs .x10).toNat ∧ (regs .x10).toNat + (regs .x12).toNat ≤ 0xc0000000)) ∧
      OffStack env (regs .x2) (regs .x10) (regs .x12).toNat ∧ inWindow (regs .x11) (regs .x12).toNat = true ∧
      OffStack env (regs .x2) (regs .x11) (regs .x12).toNat))

/-- A copy's total postcondition: `dst` returned, `[dst, dst + n)` holding what `[src, src + n)` held, and every
    byte outside it and apart from the stack below the stack pointer kept. -/
def CopyPostT (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = regs .x10 ∧
    (∀ k, k < (regs .x12).toNat →
      m'.getByte (regs .x10 + BitVec.ofNat 64 k) = m.getByte (regs .x11 + BitVec.ofNat 64 k)) ∧
    ∀ b, ¬ InRange (regs .x10) (regs .x12).toNat b → OffStack env (regs .x2) b 1 → m'.getByte b = m.getByte b

end Rv64mc.Spec.Runtime
