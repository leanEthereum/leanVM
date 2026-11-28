module

public import NativeRustcX64.Spec.Keccak
public import NativeRustcX64.Spec.Got
public import NativeRustcVmX64.Rodata.Keccak
public import NativeVm.Model.Verify
public import NativeRustcVmX64.Code.Vm.HashPair.Names
public import NativeRustcVmX64.Code.Vm.IvWord.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfFiatShamirIv.Names
public import NativeRustcVmX64.Code.Vm.Keccak256WordsOfHashWords.Names
public import NativeRustcVmX64.Code.Vm.KeccakF.Names
public import NativeRustcVmX64.Code.Vm.Names

/-!
# The contracts of `keccak.rs`'s functions and `iv_word` on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Keccak`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, the result in RAX. Each function uses the stack below RSP (`<fn>Stack`
bytes: its pushes, its frame, its callees' return addresses and stacks; `StackOk` in its
precondition also maps the return address at RSP, which `iv_word`, a leaf, only reads) and returns
with the callee-saved registers kept (and RSP 8 above, `Spec`), no byte changed outside its output
and that stack (`stackBelow`). Those that permute read the round constants, 192 bytes at `NativeRustcVmX64.Vm.Symbols.rodata1Label`
(`RcAt`, `NativeRustcVmX64/Rodata/Keccak.lean`). A state, a digest and a slice of `u64` are their
words end to end, little-endian (`NativeRustcVm.WordsAt`). The raw indirect calls read ordinary
loader-provided GOT slots (`GotAt`): `memcpy` for `keccak_f`, and `memcpy` and `memset` for its
sponge callers. The slots are disjoint from the stack, output and read-only round constants;
`iv_word` reads no GOT slot. Results are the model's (`NativeVm.Model`):

- `keccak_f(a)` (RDI): the 25 words at `a` become `keccakF1600` of them.
- `keccak256_words::<hash_words's closure>(out, count, len, ws, n)` (RDI, RSI, RDX, and the slice
  `ws` the closure captures in RCX, R8), called with `count = n`, `len = 8 n`: the 4 words at
  `out` become `hashWords ws`.
- `keccak256_words::<fiat_shamir_iv's closure>(out, count, len, bc, n)` (RDI to R8), called with
  `count = n + 2`, `len = 9 + 8 n < 2 ^ 32`: the 4 words at `out` become `fiatShamirIv bc`.
- `iv_word(bc, n, k)` (RDI, RSI, RDX): word `k` of `ivWords bc` in RAX.
- `hash_pair(out, left, right)` (RDI, RSI, RDX): the 4 words at `out` become
  `hashPair left right`.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model LeanVM.Semantics LeanVM.Parameters

@[expose] public section

/-! ## Stacks -/

/-- The stack `keccak_f` uses: 6 pushes, its 424-byte frame and `memcpy`'s return address. -/
def keccakFStack : Nat := 48 + 424 + 8
/-- The stack `keccak256_words` uses (either closure): 6 pushes, its 232-byte frame, then
`keccak_f`'s return address and stack (`memset` and `iv_word` use only their return
addresses). -/
def keccak256WordsStack : Nat := 48 + 232 + 8 + keccakFStack
/-- The stack `hash_pair` uses: its 72-byte frame, then `keccak256_words`'s return address and
stack. -/
def hashPairStack : Nat := 72 + 8 + keccak256WordsStack

section
variable [Labels]

/-! ## `keccak_f` -/

/-- `keccak_f`'s precondition. -/
def KeccakFPre (m : MachineData) : Prop :=
  let a := reg m .rdi
  StackOk m keccakFStack ∧ RcAt m keccakFStack ∧ Mapped m.dmem a 200 ∧ NoWrap a 200 ∧
    Apart a 200 (stackBelow m keccakFStack) (keccakFStack + 8) ∧ Apart a 200 rcAddr 192 ∧
    GotAt m keccakFStack [(a, 200), (rcAddr, 192)] ["memcpy"]

/-- `keccak_f`'s postcondition. -/
def KeccakFPost (m m' : MachineData) : Prop :=
  let a := reg m .rdi
  (∀ A : KeccakState, NativeRustcVm.WordsAt m.dmem a A.toList →
      NativeRustcVm.WordsAt m'.dmem a (keccakF1600 A).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange a 200 p ∨
      InRange (stackBelow m keccakFStack) keccakFStack p) ∧ Saved m m'

/-! ## `keccak256_words` -/

/-- `keccak256_words::<hash_words's closure>`'s precondition. -/
def Keccak256WordsHashPre (m : MachineData) : Prop :=
  let out := reg m .rdi; let ws := reg m .rcx; let n := (reg m .r8).toNat
  StackOk m keccak256WordsStack ∧ RcAt m keccak256WordsStack ∧
    (reg m .rsi).toNat = n ∧ (reg m .rdx).toNat = 8 * n ∧
    Mapped m.dmem ws (8 * n) ∧ NoWrap ws (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    (0 < n → Apart ws (8 * n) (stackBelow m keccak256WordsStack) (keccak256WordsStack + 8)) ∧
    Apart out 32 (stackBelow m keccak256WordsStack) (keccak256WordsStack + 8) ∧
    Apart out 32 rcAddr 192 ∧
    GotAt m keccak256WordsStack [(out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `keccak256_words::<hash_words's closure>`'s postcondition. -/
def Keccak256WordsHashPost (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let ws := reg m .rcx; let n := (reg m .r8).toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem ws w →
      NativeRustcVm.WordsAt m'.dmem out (hashWords w.toArray).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m keccak256WordsStack) keccak256WordsStack p) ∧ Saved m m'

/-- `keccak256_words::<fiat_shamir_iv's closure>`'s precondition. -/
def Keccak256WordsIvPre (m : MachineData) : Prop :=
  let out := reg m .rdi; let bc := reg m .rcx; let n := (reg m .r8).toNat
  StackOk m keccak256WordsStack ∧ RcAt m keccak256WordsStack ∧
    (reg m .rsi).toNat = n + 2 ∧ (reg m .rdx).toNat = 9 + 8 * n ∧ 9 + 8 * n < 2 ^ 32 ∧
    Mapped m.dmem bc (8 * n) ∧ NoWrap bc (8 * n) ∧ Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    (0 < n → Apart bc (8 * n) (stackBelow m keccak256WordsStack) (keccak256WordsStack + 8)) ∧
    Apart out 32 (stackBelow m keccak256WordsStack) (keccak256WordsStack + 8) ∧
    Apart out 32 rcAddr 192 ∧
    GotAt m keccak256WordsStack [(out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `keccak256_words::<fiat_shamir_iv's closure>`'s postcondition. -/
def Keccak256WordsIvPost (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let bc := reg m .rcx; let n := (reg m .r8).toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem bc w →
      NativeRustcVm.WordsAt m'.dmem out (fiatShamirIv w.toArray).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m keccak256WordsStack) keccak256WordsStack p) ∧ Saved m m'

/-! ## `iv_word`, `hash_pair` -/

/-- `iv_word`'s precondition. -/
def IvWordPre (m : MachineData) : Prop :=
  let bc := reg m .rdi; let n := (reg m .rsi).toNat
  StackOk m 0 ∧ Mapped m.dmem bc (8 * n) ∧ NoWrap bc (8 * n)

/-- `iv_word`'s postcondition. -/
def IvWordPost (m m' : MachineData) : Prop :=
  let bc := reg m .rdi; let n := (reg m .rsi).toNat
  (∀ w : List UInt64, w.length = n → NativeRustcVm.WordsAt m.dmem bc w →
      reg m' .rax = ((ivWords w.toArray).getD (reg m .rdx).toNat 0).toBitVec) ∧
    m'.dmem = m.dmem ∧ Saved m m'

/-- `hash_pair`'s precondition. -/
def HashPairPre (m : MachineData) : Prop :=
  let out := reg m .rdi; let l := reg m .rsi; let r := reg m .rdx
  StackOk m hashPairStack ∧ RcAt m hashPairStack ∧
    Mapped m.dmem l 32 ∧ NoWrap l 32 ∧ Mapped m.dmem r 32 ∧ NoWrap r 32 ∧
    Mapped m.dmem out 32 ∧ NoWrap out 32 ∧
    Apart l 32 (stackBelow m hashPairStack) (hashPairStack + 8) ∧
    Apart r 32 (stackBelow m hashPairStack) (hashPairStack + 8) ∧
    Apart out 32 (stackBelow m hashPairStack) (hashPairStack + 8) ∧ Apart out 32 rcAddr 192 ∧
    GotAt m hashPairStack [(out, 32), (rcAddr, 192)] ["memcpy", "memset"]

/-- `hash_pair`'s postcondition. -/
def HashPairPost (m m' : MachineData) : Prop :=
  let out := reg m .rdi; let l := reg m .rsi; let r := reg m .rdx
  (∀ L R : LeanVM.Protocol.Digest, NativeRustcVm.WordsAt m.dmem l L.toList →
      NativeRustcVm.WordsAt m.dmem r R.toList →
      NativeRustcVm.WordsAt m'.dmem out (hashPair L R).toList) ∧
    SameOutside m.dmem m'.dmem (fun p ↦ InRange out 32 p ∨
      InRange (stackBelow m hashPairStack) hashPairStack p) ∧ Saved m m'

end

end

end NativeRustcVmX64
