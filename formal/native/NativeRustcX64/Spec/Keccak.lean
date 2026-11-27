module

public import NativeRustcX64.Rodata.Names

public import NativeRustcX64.Spec.Mem
public import NativeRustcX64.Spec.Got
public import NativeRustc.Keccak.Hasher

/-!
# The contracts of `keccak_f`, `Hasher::update` and `Hasher::finalize`

Each reads the round constants, 192 bytes at the label `NativeRustcX64.roundConstantsLabel` (`RcAt`), and uses the stack
below RSP (`keccakFStack`, `updateStack`, `finalizeStack` bytes: its pushes, its frame, its red
zone and its callees' stacks with their return addresses; `StackOk` also maps the return address
at RSP). Each returns with the callee-saved registers kept (and RSP 8 above, `Spec`), and changes no
byte outside its outputs and its stack.
The hasher entry points also require the loader's GOT slots, disjoint from their full stack
budget and their input/output areas. `keccak_f` does not use the GOT.

- `keccak_f(a)` (RDI): the 200 bytes at `a` become `Keccak.keccakF` of them.
- `Hasher::update(h, data, n)` (RDI, RSI, RDX): a hasher at `h` (344 bytes) that has absorbed
  `absorbed` becomes one that has absorbed `absorbed ++ data` (`Keccak.HasherHolds`); returns `h`
  in RAX.
- `Hasher::finalize(out, h)` (RDI, RSI): the 32 bytes at `out` become `Keccak.finalize` of the
  hasher at `h`, `keccak256` of what it has absorbed (`Keccak.finalize_eq`).
-/

namespace NativeRustcX64

open NativeRustc

@[expose] public section


/-- The round constants' bytes: the 24 constants, little-endian. -/
def rcBytes : List UInt8 := LeanVM.Parameters.keccakRC.flatMap LeanVM.Protocol.KeccakHash.wordBytes

/-- The stack `keccak_f` uses: 6 pushes, a 112-byte frame and the 128-byte red zone below it. -/
def keccakFStack : Nat := 48 + 112 + 128
/-- The stack `Hasher::update` uses: 6 pushes, a 56-byte frame, then `keccak_f`'s return address
and stack (`memcpy` uses only its return address). -/
def updateStack : Nat := 48 + 56 + 8 + keccakFStack
/-- The stack `Hasher::finalize` uses: 4 pushes, a 344-byte frame, then `keccak_f`'s return
address and stack. -/
def finalizeStack : Nat := 32 + 344 + 8 + keccakFStack

/-- The `n` bytes below RSP. -/
def stackBelow (m : MachineData) (n : Nat) : BitVec 64 := rspOf m - BitVec.ofNat 64 n

section
variable [Labels]

/-- The address of the round constants. -/
def rcAddr : BitVec 64 := (label NativeRustcX64.roundConstantsLabel).toBitVec

/-- The round constants are at their label, apart from the `n` bytes below RSP and the return
address at RSP. -/
def RcAt (m : MachineData) (n : Nat) : Prop :=
  BytesAt m.dmem rcAddr rcBytes ∧ NoWrap rcAddr 192 ∧ Apart rcAddr 192 (stackBelow m n) (n + 8)

/-- `keccak_f`'s precondition. -/
def KeccakFPre (m : MachineData) : Prop :=
  let a := reg m .rdi
  StackOk m keccakFStack ∧ RcAt m keccakFStack ∧ Mapped m.dmem a 200 ∧ NoWrap a 200 ∧
    Apart a 200 (stackBelow m keccakFStack) (keccakFStack + 8) ∧ Apart a 200 rcAddr 192

/-- `keccak_f`'s postcondition. -/
def KeccakFPost (m m' : MachineData) : Prop :=
  let a := reg m .rdi
  BytesAt m'.dmem a (Keccak.keccakF (bytesOf m.dmem a 200)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange a 200 p ∨ InRange (stackBelow m keccakFStack)
      keccakFStack p) ∧ Saved m m'

/-- `Hasher::update`'s precondition, including the read-only `memcpy` GOT slot. -/
def UpdatePre (m : MachineData) : Prop :=
  let h := reg m .rdi; let d := reg m .rsi; let n := (reg m .rdx).toNat
  StackOk m updateStack ∧ RcAt m updateStack ∧ (∃ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a) ∧
    Mapped m.dmem h 344 ∧ NoWrap h 344 ∧ Mapped m.dmem d n ∧ NoWrap d n ∧ Apart h 344 d n ∧
    Apart h 344 (stackBelow m updateStack) (updateStack + 8) ∧
    Apart d n (stackBelow m updateStack) (updateStack + 8) ∧ Apart h 344 rcAddr 192 ∧
    GotAt m updateStack [(h, 344), (d, n)] ["memcpy"]

/-- `Hasher::update`'s precondition under `ElfHost`: the read-only `memcpy` GOT slot only needs to
be disjoint from the writable stack and hasher state `h`, not from the read-only input buffer `d`. -/
def UpdatePreElf (m : MachineData) : Prop :=
  let h := reg m .rdi; let d := reg m .rsi; let n := (reg m .rdx).toNat
  StackOk m updateStack ∧ RcAt m updateStack ∧ (∃ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a) ∧
    Mapped m.dmem h 344 ∧ NoWrap h 344 ∧ Mapped m.dmem d n ∧ NoWrap d n ∧ Apart h 344 d n ∧
    Apart h 344 (stackBelow m updateStack) (updateStack + 8) ∧
    Apart d n (stackBelow m updateStack) (updateStack + 8) ∧ Apart h 344 rcAddr 192 ∧
    GotAt m updateStack [(h, 344)] ["memcpy"]

theorem UpdatePre.toUpdatePreElf {m : MachineData} (h : UpdatePre m) : UpdatePreElf m :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.areas (by simp)⟩

/-- `Hasher::update`'s postcondition. -/
def UpdatePost (m m' : MachineData) : Prop :=
  let h := reg m .rdi; let d := reg m .rsi; let n := (reg m .rdx).toNat
  reg m' .rax = h ∧
    (∀ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a →
      Keccak.HasherHolds (bytesOf m'.dmem h 344) (a ++ bytesOf m.dmem d n)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange h 344 p ∨ InRange (stackBelow m updateStack)
      updateStack p) ∧ Saved m m'

/-- `Hasher::finalize`'s precondition, including the read-only memory-routine GOT slots. -/
def FinalizePre (m : MachineData) : Prop :=
  let o := reg m .rdi; let h := reg m .rsi
  StackOk m finalizeStack ∧ RcAt m finalizeStack ∧
    (∃ a, Keccak.HasherHolds (bytesOf m.dmem h 344) a) ∧ Mapped m.dmem h 344 ∧ NoWrap h 344 ∧
    Mapped m.dmem o 32 ∧ NoWrap o 32 ∧ Apart o 32 h 344 ∧
    Apart h 344 (stackBelow m finalizeStack) (finalizeStack + 8) ∧
    Apart o 32 (stackBelow m finalizeStack) (finalizeStack + 8) ∧ Apart o 32 rcAddr 192 ∧
    GotAt m finalizeStack [(o, 32), (h, 344)] ["memcpy", "memset"]

/-- `Hasher::finalize`'s postcondition. -/
def FinalizePost (m m' : MachineData) : Prop :=
  let o := reg m .rdi; let h := reg m .rsi
  BytesAt m'.dmem o (Keccak.finalize (bytesOf m.dmem h 344)) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange o 32 p ∨ InRange (stackBelow m finalizeStack)
      finalizeStack p) ∧ Saved m m'

end

end

end NativeRustcX64
