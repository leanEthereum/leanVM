/-
  Rv64mc.Spec.Runtime.Mem

  The contracts of the C memory functions the image calls (`memcpy`, `memmove`, `memset`, `memcmp`, each a tail
  call of `compiler_builtins`' own), on bytes: `getByte`, riscv-zkvm's byte of its doubleword. A function that
  writes `[dst, dst + n)` may write the doublewords that hold it (`DwordsOf`), and keeps every byte outside it
  (`ByteFrame`).
-/

import Rv64mc.Core.Repr

namespace Rv64mc.Spec.Runtime

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- The doublewords that hold the bytes `[a, a + n)`. -/
def DwordsOf (a : Word) (n : Nat) (b : Word) : Prop := InRange (alignToDword a) (n + a.toNat % 8) b

/-- The bytes `[a, a + n)` do not wrap around. -/
def NoWrap (a : Word) (n : Nat) : Prop := a.toNat + n < 2 ^ 64

/-! ## `memcpy`, `memmove` -/

/-- `memcpy(dst, src, n)` and `memmove`'s precondition: neither range wraps; `memcpy`'s do not overlap. -/
def CopyPre (overlap : Bool) (regs : Reg → Word) (_m : MachineState) : Prop :=
  NoWrap (regs .x10) (regs .x12).toNat ∧ NoWrap (regs .x11) (regs .x12).toNat ∧
    (overlap = false → ∀ b, InRange (regs .x10) (regs .x12).toNat b → ¬ InRange (regs .x11) (regs .x12).toNat b)

/-- The copy's postcondition: `dst` returned, `[dst, dst + n)` holds what `[src, src + n)` held, every other byte
    kept. -/
def CopyPost (regs : Reg → Word) (m : MachineState) (r' : Reg → Word) (m' : MachineState) : Prop :=
  r' .x10 = regs .x10 ∧
    (∀ k, k < (regs .x12).toNat →
      m'.getByte (regs .x10 + BitVec.ofNat 64 k) = m.getByte (regs .x11 + BitVec.ofNat 64 k)) ∧
    ByteFrame m m' (regs .x10) (regs .x12).toNat

/-- What a copy may write: the doublewords of its destination. -/
def CopyOut (regs : Reg → Word) (_m : MachineState) : Word → Prop := DwordsOf (regs .x10) (regs .x12).toNat

/-- **`memcpy`'s contract.** -/
def MemcpySpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (CopyPre false) CopyPost CopyOut

/-- **`memmove`'s contract**: the ranges may overlap. -/
def MemmoveSpec (env : Env) (p : Lprog (Op Reg) Reg) (i need : Nat) : Prop :=
  Holds env p i need (CopyPre true) CopyPost CopyOut

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
