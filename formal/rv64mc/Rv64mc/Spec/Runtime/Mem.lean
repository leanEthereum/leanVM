/-
  Rv64mc.Spec.Runtime.Mem

  The contracts of the C memory functions the image calls (`memcpy`, `memmove`, `memset`, `memcmp`, each a tail
  call of `compiler_builtins`' own), on bytes: `getByte`, riscv-zkvm's byte of its doubleword. A function that
  writes `[dst, dst + n)` may write the doublewords that hold it (`DwordsOf`), and keeps every byte outside it
  (`ByteFrame`).

  `memcpy` and `memmove` do not keep it: both keep scratch in a stack slot below the stack pointer at entry
  (`memcpy`'s `load_aligned_partial` assembles a partial word there when the source is not 8-byte aligned against
  the destination; `memmove` saves `s0` there) and leave it changed (`Table/CopyScratch.lean`). So a copy keeps every
  byte outside the destination and apart from the stack below the stack pointer (`CopyPost`, `OffStack`), which is
  all a caller can read afterwards, and its source and destination must lie apart from that stack, the destination
  also apart from the static data and `NEXT` (`CopyApart`): the caller's objects, at or above its stack pointer or
  below `NEXT`.
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The doublewords that hold the bytes `[a, a + n)`. -/
def DwordsOf (a : Word) (n : Nat) (b : Word) : Prop := InRange (alignToDword a) (n + a.toNat % 8) b

/-- The bytes `[a, a + n)` do not wrap around. -/
def NoWrap (a : Word) (n : Nat) : Prop := a.toNat + n < 2 ^ 64

/-- The bytes `[a, a + n)` lie below the stack's limit or at or above `sp`: apart from the stack below `sp`. -/
def OffStack (env : Env) (sp a : Word) (n : Nat) : Prop :=
  a.toNat + n ≤ env.stackLimit.toNat ∨ sp.toNat ≤ a.toNat

/-! ## `memcpy`, `memmove` -/

/-- `memcpy(dst, src, n)` and `memmove`'s precondition: neither range wraps; `memcpy`'s do not overlap. -/
def CopyPre (overlap : Bool) (regs : Reg → Word) (_m : MachineState) : Prop :=
  NoWrap (regs .x10) (regs .x12).toNat ∧ NoWrap (regs .x11) (regs .x12).toNat ∧
    (overlap = false → ∀ b, InRange (regs .x10) (regs .x12).toNat b → ¬ InRange (regs .x11) (regs .x12).toNat b)

/-- Where a copy's ranges lie, unless there are no bytes: the destination a caller's object (`Env.Owned`), the
    source apart from the stack below the stack pointer. `memcpy` copies a range on its slot wrong
    (`Table/CopyScratch.lean`); `Owned` asks more than that (not `[NEXT, heapEnd)`), and every caller has it. -/
def CopyApart (env : Env) (regs : Reg → Word) (m : MachineState) : Prop :=
  (regs .x12).toNat = 0 ∨
    (env.Owned m (regs .x2) (regs .x10) (regs .x12).toNat ∧ OffStack env (regs .x2) (regs .x11) (regs .x12).toNat)

/-- The copy's postcondition: `dst` returned, `[dst, dst + n)` holds what `[src, src + n)` held, every other byte
    apart from the stack below the stack pointer kept. -/
def CopyPost (env : Env) (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = regs .x10 ∧
    (∀ k, k < (regs .x12).toNat →
      m'.getByte (regs .x10 + BitVec.ofNat 64 k) = m.getByte (regs .x11 + BitVec.ofNat 64 k)) ∧
    ∀ b, ¬ InRange (regs .x10) (regs .x12).toNat b → OffStack env (regs .x2) b 1 → m'.getByte b = m.getByte b

/-- What a copy may write: the doublewords of its destination. -/
def CopyOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := DwordsOf (regs .x10) (regs .x12).toNat

/-- **`memcpy`'s contract.** -/
def MemcpySpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun regs m => CopyPre false regs m ∧ CopyApart env regs m) (CopyPost env) CopyOut

/-- **`memmove`'s contract**: the ranges may overlap. -/
def MemmoveSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun regs m => CopyPre true regs m ∧ CopyApart env regs m) (CopyPost env) CopyOut

/-! ## `memset` -/

/-- `memset(dst, c, n)`'s precondition: the range does not wrap. -/
def SetPre (regs : Reg → Word) (_m : MachineState) : Prop := NoWrap (regs .x10) (regs .x12).toNat

/-- `memset`'s postcondition: `dst` returned, `[dst, dst + n)` holds `c`'s low byte, every other byte kept. -/
def SetPost (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = regs .x10 ∧
    (∀ k, k < (regs .x12).toNat → m'.getByte (regs .x10 + BitVec.ofNat 64 k) = (regs .x11).setWidth 8) ∧
    ByteFrame m m' (regs .x10) (regs .x12).toNat

/-- **`memset`'s contract.** -/
def MemsetSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need SetPre SetPost CopyOut

/-! ## `memcmp` -/

/-- What `memcmp` returns on two byte strings: the difference of the first two bytes that differ, as `u8`s
    widened, or zero. -/
def memcmpVal : List (BitVec 8) → List (BitVec 8) → Word
  | x :: xs, y :: ys => if x = y then memcmpVal xs ys else x.setWidth 64 - y.setWidth 64
  | _, _ => 0

/-- The `n` bytes from `a`. -/
def bytesFrom (m : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun k => m.getByte (a + BitVec.ofNat 64 k)

/-- `memcmp(a, b, n)`'s postcondition: the comparison of the two byte strings; memory is not written. -/
def CmpPost (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (_m' : MachineState) : Prop :=
  r' .x10 = memcmpVal (bytesFrom m (regs .x10) (regs .x12).toNat) (bytesFrom m (regs .x11) (regs .x12).toNat)

/-- **`memcmp`'s contract.** -/
def MemcmpSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (fun _ _ => True) CmpPost

end Rv64mc.Spec.Runtime
