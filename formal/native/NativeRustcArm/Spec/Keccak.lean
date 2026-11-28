module

public import NativeRustcArm.Rodata.Names

public import NativeRustcArm.Spec.Mem
public import NativeRustc.Keccak.Hasher

/-!
# The contracts of `keccak_f`, `Hasher::update` and `Hasher::finalize`

Each reads the round constants, 192 bytes at the label `NativeRustcArm.roundConstantsLabel` (`RcAt`), and uses the stack
below SP (`keccakFStack`, `updateStack`, `finalizeStack` bytes, its callees' included). Each
returns with the callee-saved registers and SP kept, and changes no byte outside its outputs and its
stack.

- `keccak_f(a)` (X0): the 200 bytes at `a` become `Keccak.keccakF` of them.
- `Hasher::update(h, data, n)` (X0, X1, X2): a hasher at `h` (344 bytes) that has absorbed
  `absorbed` becomes one that has absorbed `absorbed ++ data` (`Keccak.HasherHolds`); returns `h`.
- `Hasher::finalize(out, h)` (X0, X1): the 32 bytes at `out` become `Keccak.finalize` of the hasher
  at `h`, `keccak256` of what it has absorbed (`Keccak.finalize_eq`).
-/

namespace NativeRustcArm

open NativeRustc

@[expose] public section


/-- The round constants' bytes: the 24 constants, little-endian. -/
def rcBytes : List UInt8 := LeanVM.Parameters.keccakRC.flatMap LeanVM.Protocol.KeccakHash.wordBytes

/-- The stack `keccak_f` uses. -/
def keccakFStack : Nat := 192
/-- The stack `Hasher::update` uses, `keccak_f`'s included. -/
def updateStack : Nat := 64 + keccakFStack
/-- The stack `Hasher::finalize` uses, `keccak_f`'s included. -/
def finalizeStack : Nat := 384 + keccakFStack

/-- The `n` bytes below SP. -/
def stackBelow (m : MachineData) (n : Nat) : BitVec 64 := m.regs.SP.toBitVec - BitVec.ofNat 64 n

section
variable [Labels]

/-- The address of the round constants. -/
def rcAddr : BitVec 64 := (label NativeRustcArm.roundConstantsLabel).toBitVec

/-- The round constants are at their label, apart from the `n` bytes below SP. -/
def RcAt (m : MachineData) (n : Nat) : Prop :=
  BytesAt m.dmem rcAddr rcBytes ∧ NoWrap rcAddr 192 ∧ Apart rcAddr 192 (stackBelow m n) n

/-- `keccak_f`'s precondition. -/
def KeccakFPre (m : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  StackOk m keccakFStack ∧ RcAt m keccakFStack ∧ Mapped m.dmem a 200 ∧ NoWrap a 200 ∧
    Apart a 200 (stackBelow m keccakFStack) keccakFStack ∧ Apart a 200 rcAddr 192

/-- `keccak_f`'s postcondition. -/
def KeccakFPost (m m' : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  BytesAt m'.dmem a (Keccak.keccakF (bytesOf m.dmem a 200)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange a 200 p ∨ InRange (stackBelow m keccakFStack)
      keccakFStack p) ∧ Saved m m'

/-- `Hasher::update`'s precondition. -/
def UpdatePre (m : MachineData) : Prop :=
  let h := m.regs.X0.toBitVec; let d := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  StackOk m updateStack ∧ RcAt m updateStack ∧ (∃ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a) ∧
    Mapped m.dmem h 344 ∧ NoWrap h 344 ∧ Mapped m.dmem d n ∧ NoWrap d n ∧ Apart h 344 d n ∧
    Apart h 344 (stackBelow m updateStack) updateStack ∧ Apart d n (stackBelow m updateStack) updateStack ∧
    Apart h 344 rcAddr 192

/-- `Hasher::update`'s postcondition. -/
def UpdatePost (m m' : MachineData) : Prop :=
  let h := m.regs.X0.toBitVec; let d := m.regs.X1.toBitVec; let n := m.regs.X2.toNat
  m'.regs.X0 = m.regs.X0 ∧
    (∀ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a →
      Keccak.HasherHolds (bytesOf m'.dmem h 344) (a ++ bytesOf m.dmem d n)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange h 344 p ∨ InRange (stackBelow m updateStack)
      updateStack p) ∧ Saved m m'

/-- `Hasher::finalize`'s precondition. -/
def FinalizePre (m : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let h := m.regs.X1.toBitVec
  StackOk m finalizeStack ∧ RcAt m finalizeStack ∧
    (∃ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a) ∧ Mapped m.dmem h 344 ∧ NoWrap h 344 ∧
    Mapped m.dmem o 32 ∧ NoWrap o 32 ∧ Apart o 32 h 344 ∧
    Apart h 344 (stackBelow m finalizeStack) finalizeStack ∧
    Apart o 32 (stackBelow m finalizeStack) finalizeStack ∧ Apart o 32 rcAddr 192

/-- `Hasher::finalize`'s postcondition. -/
def FinalizePost (m m' : MachineData) : Prop :=
  let o := m.regs.X0.toBitVec; let h := m.regs.X1.toBitVec
  BytesAt m'.dmem o (Keccak.finalize (bytesOf m.dmem h 344)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 32 p ∨ InRange (stackBelow m finalizeStack)
      finalizeStack p) ∧ Saved m m'

end

end

end NativeRustcArm
