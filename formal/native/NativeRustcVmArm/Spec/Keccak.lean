module

public import NativeRustcVmArm.Code.Vm.HashPair.Names
public import NativeRustcVmArm.Code.Vm.IvWord.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmArm.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmArm.Code.Vm.KeccakF.Names
public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcArm.Spec.Keccak
public import NativeRustcVm.Mem
public import NativeVm.Model.Verify

/-!
# The contracts of `keccak.rs`'s functions and `iv_word` on AArch64

Each function uses the stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its
precondition; `iv_word` uses none) and returns with the callee-saved registers and SP kept, no byte
changed outside its output and that stack (`stackBelow`). Those that permute read the round
constants, 192 bytes at `NativeRustcVmArm.Vm.Symbols.rodata1Label` (`RcAt`). A state, a digest and a slice of `u64` are their
words end to end, little-endian (`NativeRustcVm.WordsAt`). Results are the model's
(`NativeVm.Model`):

- `keccak_f(a)` (X0): the 25 words at `a` become `keccakF1600` of them.
- `keccak256_words::<hash_words's closure>(out, count, len, ws, n)` (X0, X1, X2, and the slice
  `ws` the closure captures in X3, X4), called with `count = n`, `len = 8 n`: the 4 words at
  `out` become `hashWords ws`.
- `keccak256_words::<fiat_shamir_iv's closure>(out, count, len, bc, n)` (X0 to X4), called with
  `count = n + 2`, `len = 9 + 8 n < 2 ^ 32` (rustc divides `len` by `136` in 32 bits): the 4
  words at `out` become `fiatShamirIv bc`.
- `iv_word(bc, n, k)` (X0, X1, X2): word `k` of `ivWords bc` in X0.
- `hash_pair(out, left, right)` (X0, X1, X2): the 4 words at `out` become `hashPair left right`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model LeanVM.Semantics LeanVM.Parameters

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The stack `keccak_f` uses: its 400-byte frame (`memcpy` uses none). -/
def keccakFStack : Nat := 400
/-- The stack `keccak256_words` uses (either closure): its 288-byte frame and `keccak_f`'s
(`memset` and `iv_word` use none). -/
def keccak256WordsStack : Nat := 288 + keccakFStack
/-- The stack `hash_pair` uses: its 80-byte frame and `keccak256_words`'s. -/
def hashPairStack : Nat := 80 + keccak256WordsStack

section
variable [Labels]

/-- The address of the round constants. -/
def rcAddr : BitVec 64 := (label NativeRustcVmArm.Vm.Symbols.rodata1Label).toBitVec

/-- The round constants are at their label, apart from the `n` bytes below SP. -/
def RcAt (m : MachineData) (n : Nat) : Prop :=
  NativeRustcVm.WordsAt m.dmem rcAddr keccakRC ∧ NoWrap rcAddr 192 ∧
    Apart rcAddr 192 (stackBelow m n) n

/-! ## `keccak_f` -/

/-- `keccak_f`'s precondition. -/
def KeccakFPre (m : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  StackOk m keccakFStack ∧ RcAt m keccakFStack ∧ Mapped m.dmem a 200 ∧ NoWrap a 200 ∧
    Apart a 200 (stackBelow m keccakFStack) keccakFStack ∧ Apart a 200 rcAddr 192

/-- `keccak_f`'s postcondition. -/
def KeccakFPost (m m' : MachineData) : Prop :=
  let a := m.regs.X0.toBitVec
  (∀ A : KeccakState, NativeRustcVm.WordsAt m.dmem a A.toList →
      NativeRustcVm.WordsAt m'.dmem a (keccakF1600 A).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange a 200 p ∨
      InRange (stackBelow m keccakFStack) keccakFStack p) ∧ Saved m m'

/-! ## `keccak256_words` -/

/-- `keccak256_words::<hash_words's closure>`'s precondition. -/
def Keccak256WordsHashPre (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let ws := m.regs.X3.toBitVec; let n := m.regs.X4.toNat
  StackOk m keccak256WordsStack ∧ RcAt m keccak256WordsStack ∧
    m.regs.X1.toNat = n ∧ m.regs.X2.toNat = 8 * n ∧
    Mapped m.dmem ws (8 * n) ∧ NoWrap ws (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    (0 < n → Apart ws (8 * n) (stackBelow m keccak256WordsStack) keccak256WordsStack) ∧
    Apart out 32 (stackBelow m keccak256WordsStack) keccak256WordsStack ∧ Apart out 32 rcAddr 192

/-- `keccak256_words::<hash_words's closure>`'s postcondition. -/
def Keccak256WordsHashPost (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let ws := m.regs.X3.toBitVec; let n := m.regs.X4.toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem ws w →
      NativeRustcVm.WordsAt m'.dmem out (hashWords w.toArray).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m keccak256WordsStack) keccak256WordsStack p) ∧ Saved m m'

/-- `keccak256_words::<fiat_shamir_iv's closure>`'s precondition. -/
def Keccak256WordsIvPre (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let bc := m.regs.X3.toBitVec; let n := m.regs.X4.toNat
  StackOk m keccak256WordsStack ∧ RcAt m keccak256WordsStack ∧
    m.regs.X1.toNat = n + 2 ∧ m.regs.X2.toNat = 9 + 8 * n ∧ 9 + 8 * n < 2 ^ 32 ∧
    Mapped m.dmem bc (8 * n) ∧ NoWrap bc (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    (0 < n → Apart bc (8 * n) (stackBelow m keccak256WordsStack) keccak256WordsStack) ∧
    Apart out 32 (stackBelow m keccak256WordsStack) keccak256WordsStack ∧ Apart out 32 rcAddr 192

/-- `keccak256_words::<fiat_shamir_iv's closure>`'s postcondition. -/
def Keccak256WordsIvPost (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let bc := m.regs.X3.toBitVec; let n := m.regs.X4.toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem bc w →
      NativeRustcVm.WordsAt m'.dmem out (fiatShamirIv w.toArray).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m keccak256WordsStack) keccak256WordsStack p) ∧ Saved m m'

/-! ## `iv_word`, `hash_pair` -/

/-- `iv_word`'s precondition. -/
def IvWordPre (m : MachineData) : Prop :=
  let bc := m.regs.X0.toBitVec; let n := m.regs.X1.toNat
  Mapped m.dmem bc (8 * n) ∧ NoWrap bc (8 * n)

/-- `iv_word`'s postcondition. -/
def IvWordPost (m m' : MachineData) : Prop :=
  let bc := m.regs.X0.toBitVec; let n := m.regs.X1.toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem bc w →
      m'.regs.X0 = (ivWords w.toArray).getD m.regs.X2.toNat 0) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-- `hash_pair`'s precondition. -/
def HashPairPre (m : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let l := m.regs.X1.toBitVec; let r := m.regs.X2.toBitVec
  StackOk m hashPairStack ∧ RcAt m hashPairStack ∧
    Mapped m.dmem l 32 ∧ NoWrap l 32 ∧ Mapped m.dmem r 32 ∧ NoWrap r 32 ∧
    Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart l 32 (stackBelow m hashPairStack) hashPairStack ∧
    Apart r 32 (stackBelow m hashPairStack) hashPairStack ∧
    Apart out 32 (stackBelow m hashPairStack) hashPairStack ∧ Apart out 32 rcAddr 192

/-- `hash_pair`'s postcondition. -/
def HashPairPost (m m' : MachineData) : Prop :=
  let out := m.regs.X0.toBitVec; let l := m.regs.X1.toBitVec; let r := m.regs.X2.toBitVec
  (∀ L R : LeanVM.Protocol.Digest, NativeRustcVm.WordsAt m.dmem l L.toList →
      NativeRustcVm.WordsAt m.dmem r R.toList →
      NativeRustcVm.WordsAt m'.dmem out (hashPair L R).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m hashPairStack) hashPairStack p) ∧ Saved m m'

end

end

end NativeRustcVmArm
