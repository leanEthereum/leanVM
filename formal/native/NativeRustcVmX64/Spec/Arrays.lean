module

public import NativeRustcVmX64.Basic
public import NativeRustcVmX64.Spec.Field
public import NativeRustcVm.Arrays.Read
public import NativeRustcVmX64.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmX64.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmX64.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EqEval.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmX64.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmX64.Code.Vm.PaddingWeight.Names
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names
public import NativeRustcVmX64.Code.Vm.ProdE.Names
public import NativeRustcVmX64.Code.Vm.SelectorPoint.Names
public import NativeRustcVmX64.Code.Vm.SumE.Names

/-!
# The contracts of `field.rs`'s array functions and `Buf::extend` on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Arrays`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, an `E` result in RAX, RDX, a `bool` result in AL. A slice argument is a
pointer and a length in two registers; its elements are read as `NativeRustcVm.ewsOf`
(`wordsOf` for `u64`s) gives them. An `EW` argument or result is two registers, limb `0` first
(`ewArg`, `ewRet`). Each function uses the stack below RSP (`<fn>Stack` bytes: its pushes, its
frame, its callees' return addresses and stacks; `StackOk` also maps its return address at RSP),
its slices are mapped, do not wrap and are apart from that stack and the return address
(`Readable`, `OffStack`), and it returns with the callee-saved registers kept (and RSP 8 above,
`Spec`), no byte changed outside its outputs and that stack. The results are the model's
(`NativeVm.Model`):

- `sum_e(values)` (RDI, RSI): `sumE` in RAX, RDX, for `len ≤ 16` (AArch64's bound, where rustc
  unrolled the loop for its callers' lengths; the x86-64 loop is general).
- `prod_e(values)` (RDI, RSI): `prodE` in RAX, RDX, for `2 ≤ len ≤ 4` (AArch64's bound: its
  only caller's lengths; the x86-64 loop is bottom-tested).
- `dot(left, right)` (RDI-RCX): `dot` in RAX, RDX.
- `powers(base, out)` (`base` in RDI, RSI; `out` RDX, RCX): `out` holds `powers base |out|`.
- `eq_eval(left, right)` (RDI-RCX): `eqEval` in RAX, RDX.
- `eq_kernel(point, out)` (RDI-RCX): `Some(2^|point|)` (RAX = 1, RDX) with `out`'s first
  `2^|point|` elements `eqKernel point`, or `None` (RAX = 0) when `out` is shorter. The shift
  `1 << |point|` is `shl` by CL (modulo 64): `|point| < 64`.
- `poly_eval(coefficients, point)` (RDI, RSI; `point` RDX, RCX): `polyEval` in RAX, RDX, for
  `1 ≤ |coefficients|` (a bottom-tested loop).
- `index_mle_from(GEN, point)` (RDI, RSI; the generator power specialised to `GEN`):
  `indexMleFrom gen point` in RAX, RDX.
- `padding_weight(point, n)` (RDI, RSI; RDX): `paddingWeight point n` in RAX, RDX. The shifts
  are `shr` by CL (modulo 64): `|point| < 64`.
- `selector_point(selector, out)` (RDI; RSI, RDX): `out` holds `selectorPoint selector |out|`.
  Its raw `bt`s select register bits without accessing memory.
- `eq_eval_fn(n, |k| bit_e(selector, k), right)` (RDI, RSI, RDX, RCX; `eq_above`'s closure):
  `eqEval (selectorPoint selector n) right` in RAX, RDX. The `bt`s take the bit index modulo 64:
  `min n |right| ≤ 64`.
- `multilinear_eval_by(n, |i| mle[i], point)` (RDI; `mle` RSI, RDX; `point` RCX, R8;
  `n = |mle|`): `multilinearEval mle point` in RAX, RDX, for `|point| < 64`.
- `multilinear_eval_by(n, |i| EW::of_k(words[i]), point)` (`computed_bytecode_value`'s closure;
  RDI; `words` RSI, RDX; `point` RCX, R8; `n = |words|`): `multilinearEval (words.map EW.ofK)
  point` in RAX, RDX.
- `Buf<EW, N>::extend(self, xs)` (RDI; RSI, RDX; `N ∈ {30, 36, 63, 230}`) and
  `Buf<u64, 230>::extend`: AL = 1 (`Some`) and the buffer holds its entries then `xs` when they
  fit, else AL = 0 (`None`, the buffer's bytes changed, as Rust's partial pushes leave them).
  `Buf<EW, N>::extend` pushes RBX.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model
open NativeRustcVm (ewsOf wordsOf wordOf bufEWOf bufWordsOf BufEWAt BufWordsAt EWsAt)

@[expose] public section

/-! ## Stacks -/

/-- `sum_e` uses no stack. -/
def sumEStack : Nat := 0
/-- The stack `prod_e` uses: 3 pushes, `EW::mul`'s return address and stack. -/
def prodEStack : Nat := 32 + ewMulStack
/-- The stack `dot` uses: 7 pushes, `EW::mul`'s return address and stack. -/
def dotStack : Nat := 64 + ewMulStack
/-- The stack `powers` uses: 5 pushes, `EW::mul`'s return address and stack. -/
def powersStack : Nat := 48 + ewMulStack
/-- The stack `eq_eval` uses: 5 pushes, `EW::mul`'s return address and stack. -/
def eqEvalStack : Nat := 48 + ewMulStack
/-- The stack `eq_kernel` uses: 6 pushes, its 56-byte frame, `EW::mul`'s return address and
stack. -/
def eqKernelStack : Nat := 112 + ewMulStack
/-- The stack `poly_eval` uses: 7 pushes, `EW::mul`'s return address and stack. -/
def polyEvalStack : Nat := 64 + ewMulStack
/-- The stack `index_mle_from` uses: 7 pushes, `EW::mul`'s return address and stack. -/
def indexMleFromStack : Nat := 64 + ewMulStack
/-- The stack `padding_weight` uses: 6 pushes, its 56-byte frame, `EW::mul`'s return address and
stack (its tail call's stack is within). -/
def paddingWeightStack : Nat := 112 + ewMulStack
/-- The existing `selector_point` contract reserves 16 bytes; raw `bt` uses no stack. -/
def selectorPointStack : Nat := 16
/-- The stack `eq_eval_fn` uses: 5 pushes, `EW::mul`'s return address and stack. -/
def eqEvalFnStack : Nat := 48 + ewMulStack
/-- The stack `multilinear_eval_by` uses: 6 pushes, its 1160-byte frame (the pending entries and
the `full` flags), `EW::mul`'s return address and stack. -/
def mleStack : Nat := 1216 + ewMulStack
/-- `Buf<EW, N>::extend` pushes RBX. -/
def bufEWExtendStack : Nat := 8
/-- `Buf<u64, N>::extend` uses no stack. -/
def bufU64ExtendStack : Nat := 0

/-! ## Arguments -/

/-- An `E` element in two registers, limb `0` first. -/
def ewArg (lo hi : BitVec 64) : EW := ⟨.ofBitVec lo, .ofBitVec hi⟩

/-- The `E` element a function returns: RAX, RDX. -/
def ewRet (m : MachineData) : EW := ewArg (reg m .rax) (reg m .rdx)

/-- The `n` bytes from `a` are data memory and do not wrap around. -/
def Readable (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n

/-- The `n` bytes from `a` are apart from the `s` bytes of stack below RSP and the return address
at RSP. -/
def OffStack (m : MachineData) (a : BitVec 64) (n s : Nat) : Prop :=
  Apart a n (stackBelow m s) (s + 8)

/-- The elements of the slice (`a`, `n`): `n` elements of `E` from `a`. -/
def slice (m : MachineData) (a n : BitVec 64) : Array EW :=
  (ewsOf m.dmem a n.toNat).toArray

/-- A readable slice of `n` elements of `E` from `a`, apart from the `s` bytes below RSP and the
return address. -/
def SliceOk (m : MachineData) (a n : BitVec 64) (s : Nat) : Prop :=
  Readable m a (16 * n.toNat) ∧ OffStack m a (16 * n.toNat) s

/-- Memory changes only in the `s` bytes below RSP and the `n` bytes from `a`. -/
def Changes (m m' : MachineData) (s : Nat) (a : BitVec 64) (n : Nat) : Prop :=
  SameOutside m.dmem m'.dmem (fun p ↦ InRange a n p ∨ InRange (stackBelow m s) s p)

/-! ## Contracts -/

/-- `sum_e`'s precondition: `len ≤ 16`. -/
def SumEPre (m : MachineData) : Prop :=
  StackOk m sumEStack ∧ (reg m .rsi).toNat ≤ 16 ∧
    Readable m (reg m .rdi) (16 * (reg m .rsi).toNat)

/-- `sum_e`'s postcondition. -/
def SumEPost (m m' : MachineData) : Prop :=
  ewRet m' = sumE (slice m (reg m .rdi) (reg m .rsi)) ∧ Changes m m' sumEStack 0 0 ∧ Saved m m'

/-- `prod_e`'s precondition: `2 ≤ len ≤ 4`. -/
def ProdEPre (m : MachineData) : Prop :=
  StackOk m prodEStack ∧ 2 ≤ (reg m .rsi).toNat ∧ (reg m .rsi).toNat ≤ 4 ∧
    SliceOk m (reg m .rdi) (reg m .rsi) prodEStack

/-- `prod_e`'s postcondition. -/
def ProdEPost (m m' : MachineData) : Prop :=
  ewRet m' = prodE (slice m (reg m .rdi) (reg m .rsi)) ∧ Changes m m' prodEStack 0 0 ∧
    Saved m m'

/-- `dot`'s precondition. -/
def DotPre (m : MachineData) : Prop :=
  StackOk m dotStack ∧ SliceOk m (reg m .rdi) (reg m .rsi) dotStack ∧
    SliceOk m (reg m .rdx) (reg m .rcx) dotStack

/-- `dot`'s postcondition. -/
def DotPost (m m' : MachineData) : Prop :=
  ewRet m' = dot (slice m (reg m .rdi) (reg m .rsi)) (slice m (reg m .rdx) (reg m .rcx)) ∧
    Changes m m' dotStack 0 0 ∧ Saved m m'

/-- `powers`'s precondition. -/
def PowersPre (m : MachineData) : Prop :=
  StackOk m powersStack ∧ SliceOk m (reg m .rdx) (reg m .rcx) powersStack

/-- `powers`'s postcondition. -/
def PowersPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem (reg m .rdx) (powers (ewArg (reg m .rdi) (reg m .rsi)) (reg m .rcx).toNat).toList ∧
    Changes m m' powersStack (reg m .rdx) (16 * (reg m .rcx).toNat) ∧ Saved m m'

/-- `eq_eval`'s precondition. -/
def EqEvalPre (m : MachineData) : Prop :=
  StackOk m eqEvalStack ∧ SliceOk m (reg m .rdi) (reg m .rsi) eqEvalStack ∧
    SliceOk m (reg m .rdx) (reg m .rcx) eqEvalStack

/-- `eq_eval`'s postcondition. -/
def EqEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = eqEval (slice m (reg m .rdi) (reg m .rsi)) (slice m (reg m .rdx) (reg m .rcx)) ∧
    Changes m m' eqEvalStack 0 0 ∧ Saved m m'

/-- `eq_kernel`'s precondition: `|point| < 64`, `out` apart from `point`. -/
def EqKernelPre (m : MachineData) : Prop :=
  StackOk m eqKernelStack ∧ (reg m .rsi).toNat < 64 ∧
    SliceOk m (reg m .rdi) (reg m .rsi) eqKernelStack ∧
    SliceOk m (reg m .rdx) (reg m .rcx) eqKernelStack ∧
    Apart (reg m .rdi) (16 * (reg m .rsi).toNat) (reg m .rdx) (16 * (reg m .rcx).toNat)

/-- `eq_kernel`'s postcondition. -/
def EqKernelPost (m m' : MachineData) : Prop :=
  (if 2 ^ (reg m .rsi).toNat ≤ (reg m .rcx).toNat then
      reg m' .rax = 1#64 ∧ (reg m' .rdx).toNat = 2 ^ (reg m .rsi).toNat ∧
        EWsAt m'.dmem (reg m .rdx) (eqKernel (slice m (reg m .rdi) (reg m .rsi))).toList
    else reg m' .rax = 0#64) ∧
    Changes m m' eqKernelStack (reg m .rdx) (16 * (reg m .rcx).toNat) ∧ Saved m m'

/-- `poly_eval`'s precondition: at least one coefficient. -/
def PolyEvalPre (m : MachineData) : Prop :=
  StackOk m polyEvalStack ∧ 1 ≤ (reg m .rsi).toNat ∧
    SliceOk m (reg m .rdi) (reg m .rsi) polyEvalStack

/-- `poly_eval`'s postcondition. -/
def PolyEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = polyEval (slice m (reg m .rdi) (reg m .rsi)) (ewArg (reg m .rdx) (reg m .rcx)) ∧
    Changes m m' polyEvalStack 0 0 ∧ Saved m m'

/-- `index_mle_from`'s precondition. -/
def IndexMleFromPre (m : MachineData) : Prop :=
  StackOk m indexMleFromStack ∧ SliceOk m (reg m .rdi) (reg m .rsi) indexMleFromStack

/-- `index_mle_from`'s postcondition. -/
def IndexMleFromPost (m m' : MachineData) : Prop :=
  ewRet m' = indexMleFrom gen (slice m (reg m .rdi) (reg m .rsi)) ∧
    Changes m m' indexMleFromStack 0 0 ∧ Saved m m'

/-- `padding_weight`'s precondition: `|point| < 64`. -/
def PaddingWeightPre (m : MachineData) : Prop :=
  StackOk m paddingWeightStack ∧ (reg m .rsi).toNat < 64 ∧
    SliceOk m (reg m .rdi) (reg m .rsi) paddingWeightStack

/-- `padding_weight`'s postcondition. -/
def PaddingWeightPost (m m' : MachineData) : Prop :=
  ewRet m' = paddingWeight (slice m (reg m .rdi) (reg m .rsi)) (reg m .rdx).toNat ∧
    Changes m m' paddingWeightStack 0 0 ∧ Saved m m'

/-- `selector_point`'s precondition. -/
def SelectorPointPre (m : MachineData) : Prop :=
  StackOk m selectorPointStack ∧ Readable m (reg m .rsi) (16 * (reg m .rdx).toNat) ∧
    OffStack m (reg m .rsi) (16 * (reg m .rdx).toNat) selectorPointStack

/-- `selector_point`'s postcondition. -/
def SelectorPointPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem (reg m .rsi) (selectorPoint (reg m .rdi).toNat (reg m .rdx).toNat).toList ∧
    Changes m m' selectorPointStack (reg m .rsi) (16 * (reg m .rdx).toNat) ∧ Saved m m'

/-- `eq_eval_fn` (`eq_above`'s closure)'s precondition: `min n |right| ≤ 64`. -/
def EqEvalFnOfEqAbovePre (m : MachineData) : Prop :=
  StackOk m eqEvalFnStack ∧ min (reg m .rdi).toNat (reg m .rcx).toNat ≤ 64 ∧
    SliceOk m (reg m .rdx) (reg m .rcx) eqEvalFnStack

/-- `eq_eval_fn` (`eq_above`'s closure)'s postcondition. -/
def EqEvalFnOfEqAbovePost (m m' : MachineData) : Prop :=
  ewRet m' = eqEval (selectorPoint (reg m .rsi).toNat (reg m .rdi).toNat)
      (slice m (reg m .rdx) (reg m .rcx)) ∧
    Changes m m' eqEvalFnStack 0 0 ∧ Saved m m'

/-- `multilinear_eval_by` (`multilinear_eval`'s closure)'s precondition: `n = |mle|`,
`|point| < 64`. -/
def MleOfMultilinearEvalPre (m : MachineData) : Prop :=
  StackOk m mleStack ∧ reg m .rdi = reg m .rdx ∧ (reg m .r8).toNat < 64 ∧
    SliceOk m (reg m .rsi) (reg m .rdx) mleStack ∧ SliceOk m (reg m .rcx) (reg m .r8) mleStack

/-- `multilinear_eval_by` (`multilinear_eval`'s closure)'s postcondition. -/
def MleOfMultilinearEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = multilinearEval (slice m (reg m .rsi) (reg m .rdx))
      (slice m (reg m .rcx) (reg m .r8)) ∧
    Changes m m' mleStack 0 0 ∧ Saved m m'

/-- The words of the slice (`a`, `n`), each an `E` element in limb `0`. -/
def wordSliceE (m : MachineData) (a n : BitVec 64) : Array EW :=
  ((wordsOf m.dmem a n.toNat).map EW.ofK).toArray

/-- `multilinear_eval_by` (`computed_bytecode_value`'s closure)'s precondition: `n = |words|`. -/
def MleOfComputedBytecodeValuePre (m : MachineData) : Prop :=
  StackOk m mleStack ∧ reg m .rdi = reg m .rdx ∧
    Readable m (reg m .rsi) (8 * (reg m .rdx).toNat) ∧
    (0 < (reg m .rdx).toNat → OffStack m (reg m .rsi) (8 * (reg m .rdx).toNat) mleStack) ∧
    SliceOk m (reg m .rcx) (reg m .r8) mleStack

/-- `multilinear_eval_by` (`computed_bytecode_value`'s closure)'s postcondition. -/
def MleOfComputedBytecodeValuePost (m m' : MachineData) : Prop :=
  ewRet m' = multilinearEval (wordSliceE m (reg m .rsi) (reg m .rdx))
      (slice m (reg m .rcx) (reg m .r8)) ∧
    Changes m m' mleStack 0 0 ∧ Saved m m'

/-- `Buf<EW, N>::extend`'s precondition: a valid buffer (count at most `N`) at RDI, the slice
(RSI, RDX) apart from it, both apart from the stack. -/
def BufEWExtendPre (N : Nat) (m : MachineData) : Prop :=
  StackOk m bufEWExtendStack ∧ (wordOf m.dmem (reg m .rdi)).toNat ≤ N ∧
    Readable m (reg m .rdi) (8 + 16 * N) ∧ Readable m (reg m .rsi) (16 * (reg m .rdx).toNat) ∧
    Apart (reg m .rdi) (8 + 16 * N) (reg m .rsi) (16 * (reg m .rdx).toNat) ∧
    OffStack m (reg m .rdi) (8 + 16 * N) bufEWExtendStack ∧
    OffStack m (reg m .rsi) (16 * (reg m .rdx).toNat) bufEWExtendStack

/-- `Buf<EW, N>::extend`'s postcondition. -/
def BufEWExtendPost (N : Nat) (m m' : MachineData) : Prop :=
  (if (wordOf m.dmem (reg m .rdi)).toNat + (reg m .rdx).toNat ≤ N then
      boolRet m' = 1 ∧ BufEWAt m'.dmem (reg m .rdi) N
        (bufEWOf m.dmem (reg m .rdi) ++ (slice m (reg m .rsi) (reg m .rdx)).toList)
    else boolRet m' = 0) ∧
    Changes m m' bufEWExtendStack (reg m .rdi) (8 + 16 * N) ∧ Saved m m'

/-- `Buf<u64, 230>::extend`'s precondition. -/
def BufU64ExtendPre (N : Nat) (m : MachineData) : Prop :=
  StackOk m bufU64ExtendStack ∧ (wordOf m.dmem (reg m .rdi)).toNat ≤ N ∧
    Readable m (reg m .rdi) (8 + 8 * N) ∧ Readable m (reg m .rsi) (8 * (reg m .rdx).toNat) ∧
    Apart (reg m .rdi) (8 + 8 * N) (reg m .rsi) (8 * (reg m .rdx).toNat) ∧
    OffStack m (reg m .rdi) (8 + 8 * N) bufU64ExtendStack

/-- `Buf<u64, 230>::extend`'s postcondition. -/
def BufU64ExtendPost (N : Nat) (m m' : MachineData) : Prop :=
  (if (wordOf m.dmem (reg m .rdi)).toNat + (reg m .rdx).toNat ≤ N then
      boolRet m' = 1 ∧ BufWordsAt m'.dmem (reg m .rdi) N
        (bufWordsOf m.dmem (reg m .rdi) ++ wordsOf m.dmem (reg m .rsi) (reg m .rdx).toNat)
    else boolRet m' = 0) ∧
    Changes m m' bufU64ExtendStack (reg m .rdi) (8 + 8 * N) ∧ Saved m m'

end

end NativeRustcVmX64
