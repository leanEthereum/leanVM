module

public import NativeRustcArm.Basic

/-!
# The contracts of `memcpy` and `memset`

`memcpy(dest, src, n)` (X0, X1, X2): the `n` bytes from `src` and the `n` bytes from `dest` are
data memory, apart and not wrapping around; it returns with `dest` in X0, the `n` bytes from `dest`
those that were at `src`, every other byte as it was, and the callee-saved registers and SP kept.
`memset(dest, c, n)`: likewise with `n` copies of `c`'s low byte.
-/

namespace NativeRustcArm

@[expose] public section

/-- The `n` bytes of `d` from `a` (`0` where unmapped). -/
def bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i ↦ (d.get? (a + BitVec.ofNat 64 i)).getD 0

/-- The `n` bytes from `a` do not wrap around the address space. -/
def NoWrap (a : BitVec 64) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64

/-- The `n` bytes from `a` and the `n'` bytes from `a'` are apart. -/
def Apart (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop :=
  a.toNat + n ≤ a'.toNat ∨ a'.toNat + n' ≤ a.toNat

/-- `memcpy`'s precondition. -/
def MemcpyPre (m : MachineData) : Prop :=
  let d := m.regs.X0.toBitVec; let s := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  Mapped m.dmem d n ∧ Mapped m.dmem s n ∧ NoWrap d n ∧ NoWrap s n ∧ Apart d n s n

/-- `memcpy`'s postcondition. -/
def MemcpyPost (m m' : MachineData) : Prop :=
  let d := m.regs.X0.toBitVec; let s := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  m'.regs.X0 = m.regs.X0 ∧ BytesAt m'.dmem d (bytesOf m.dmem s n) ∧
    SameOutside m.dmem m'.dmem (InRange d n) ∧ Saved m m'

/-- `memset`'s precondition. -/
def MemsetPre (m : MachineData) : Prop :=
  Mapped m.dmem m.regs.X0.toBitVec m.regs.X2.toNat ∧ NoWrap m.regs.X0.toBitVec m.regs.X2.toNat

/-- `memset`'s postcondition. -/
def MemsetPost (m m' : MachineData) : Prop :=
  let d := m.regs.X0.toBitVec; let n := m.regs.X2.toNat
  m'.regs.X0 = m.regs.X0 ∧ BytesAt m'.dmem d (List.replicate n m.regs.X1.toUInt8) ∧
    SameOutside m.dmem m'.dmem (InRange d n) ∧ Saved m m'

end

end NativeRustcArm
