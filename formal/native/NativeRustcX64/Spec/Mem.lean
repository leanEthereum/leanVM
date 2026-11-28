module

public import NativeRustcX64.Basic

/-!
# The contracts of `memcpy` and `memset`

`memcpy(dest, src, n)` (RDI, RSI, RDX): the `n` bytes from `src` and the `n` bytes from `dest` are
data memory, apart and not wrapping around; it returns with `dest` in RAX, the `n` bytes from
`dest` those that were at `src`, every other byte as it was, and the callee-saved registers kept.
`memset(dest, c, n)` (RDI, ESI, RDX): likewise with `n` copies of `c`'s low byte. Neither uses
the stack beyond the return address `call` pushed (`StackOk m 0`).
-/

namespace NativeRustcX64

@[expose] public section

/-- The `n` bytes of `d` from `a` (`0` where unmapped). -/
def bytesOf (d : DataMem) (a : BitVec 64) (n : Nat) : List UInt8 :=
  (List.range n).map fun i ↦ (d.get? (a + BitVec.ofNat 64 i)).getD 0

/-- The `n` bytes from `a` do not wrap around the address space. -/
def NoWrap (a : BitVec 64) (n : Nat) : Prop := a.toNat + n ≤ 2 ^ 64

/-- The `n` bytes from `a` and the `n'` bytes from `a'` are apart. -/
def Apart (a : BitVec 64) (n : Nat) (a' : BitVec 64) (n' : Nat) : Prop :=
  a.toNat + n ≤ a'.toNat ∨ a'.toNat + n' ≤ a.toNat

/-- A register's value. -/
abbrev reg (m : MachineData) (r : Reg64) : BitVec 64 := m.regs.get64 r

/-- `memcpy`'s precondition; the destination apart from the return address at RSP. -/
def MemcpyPre (m : MachineData) : Prop :=
  let d := reg m .rdi; let s := reg m .rsi; let n := (reg m .rdx).toNat
  StackOk m 0 ∧ Mapped m.dmem d n ∧ Mapped m.dmem s n ∧ NoWrap d n ∧ NoWrap s n ∧
    Apart d n s n ∧ Apart d n (rspOf m) 8

/-- `memcpy`'s postcondition. -/
def MemcpyPost (m m' : MachineData) : Prop :=
  let d := reg m .rdi; let s := reg m .rsi; let n := (reg m .rdx).toNat
  reg m' .rax = d ∧ BytesAt m'.dmem d (bytesOf m.dmem s n) ∧
    SameOutside m.dmem m'.dmem (InRange d n) ∧ Saved m m'

/-- `memset`'s precondition; the destination apart from the return address at RSP. -/
def MemsetPre (m : MachineData) : Prop :=
  let d := reg m .rdi; let n := (reg m .rdx).toNat
  StackOk m 0 ∧ Mapped m.dmem d n ∧ NoWrap d n ∧ Apart d n (rspOf m) 8

/-- `memset`'s postcondition. -/
def MemsetPost (m m' : MachineData) : Prop :=
  let d := reg m .rdi; let n := (reg m .rdx).toNat
  reg m' .rax = d ∧ BytesAt m'.dmem d (List.replicate n (UInt8.ofNat (reg m .rsi).toNat)) ∧
    SameOutside m.dmem m'.dmem (InRange d n) ∧ Saved m m'

end

end NativeRustcX64
