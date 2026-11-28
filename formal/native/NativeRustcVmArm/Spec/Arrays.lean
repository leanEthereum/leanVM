module

public import NativeRustcVmArm.Code.Vm.BufEW230Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW36Extend.Names
public import NativeRustcVmArm.Code.Vm.BufEW63Extend.Names
public import NativeRustcVmArm.Code.Vm.BufU64x230Extend.Names
public import NativeRustcVmArm.Code.Vm.Dot.Names
public import NativeRustcVmArm.Code.Vm.EqEval.Names
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove.Names
public import NativeRustcVmArm.Code.Vm.EqKernel.Names
public import NativeRustcVmArm.Code.Vm.IndexMleFrom.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfComputedBytecodeValue.Names
public import NativeRustcVmArm.Code.Vm.MultilinearEvalByOfMultilinearEval.Names
public import NativeRustcVmArm.Code.Vm.PaddingWeight.Names
public import NativeRustcVmArm.Code.Vm.PolyEval.Names
public import NativeRustcVmArm.Code.Vm.Powers.Names
public import NativeRustcVmArm.Code.Vm.ProdE.Names
public import NativeRustcVmArm.Code.Vm.SelectorPoint.Names
public import NativeRustcVmArm.Code.Vm.SumE.Names
public import NativeRustcVmArm.Spec.Field
public import NativeRustcVm.Arrays.Read

/-!
# The contracts of `field.rs`'s array functions and `Buf::extend` on AArch64

A slice argument is a pointer and a length in two registers; its elements are read as
`NativeRustcVm.ewsOf` (`wordsOf` for `u64`s) gives them, so that a caller holding `EWsAt d a xs`
gets `xs` back (`ewsOf_of_ewsAt`). An `EW` argument or result is two registers, limb `0` first
(`ewArg`, `ewRet`). Each function uses the stack below SP (`<fn>Stack` bytes, `EW::mul`'s
included), its slices are mapped, do not wrap and are apart from that stack (`Readable`,
`OffStack`), and it returns with the callee-saved registers and SP kept (`Saved`), no byte changed
outside its outputs and that stack. The results are the model's (`NativeVm.Model`):

- `sum_e(values)` (X0, X1): `sumE` in X0, X1. rustc specialised the unrolled body to its callers'
  lengths: `len ≤ 16`.
- `prod_e(values)` (X0, X1): `prodE` in X0, X1. rustc specialised the body to the lengths its only
  caller (`gkr.rs`, `child.get(..1 << step)` with `step ∈ {1, 2}`) passes: `2 ≤ len ≤ 4`.
- `dot(left, right)` (X0-X3): `dot` in X0, X1.
- `powers(base, out)` (`base` in X0, X1; `out` X2, X3): `out` holds `powers base |out|`.
- `eq_eval(left, right)` (X0-X3): `eqEval` in X0, X1.
- `eq_kernel(point, out)` (X0-X3): `Some(2^|point|)` (X0 = 1, X1) with `out`'s first `2^|point|`
  elements `eqKernel point`, or `None` (X0 = 0) when `out` is shorter. The shift `1 << |point|` is
  `lsl` (modulo 64): `|point| < 64` (every caller's point is a `Buf` of at most 63 elements).
- `poly_eval(coefficients, point)` (X0, X1; `point` X2, X3): `polyEval` in X0, X1. The loop is
  bottom-tested: `1 ≤ |coefficients|` (its callers pass fixed-size, nonempty arrays and
  `msg.get(..count)` with `count ≥ 1`).
- `index_mle_from(GEN, point)` (X0, X1; rustc specialised the generator power to its only
  caller's `GEN`): `indexMleFrom gen point` (`indexMle point`) in X0, X1.
- `padding_weight(point, n)` (X0, X1; X2): `paddingWeight point n` in X0, X1. The shifts are
  `lsr` (modulo 64): `|point| < 64`.
- `selector_point(selector, out)` (X0; X1, X2): `out` holds `selectorPoint selector |out|`.
- `eq_eval_fn(n, |k| bit_e(selector, k), right)` (X0, X1, X2, X3; `eq_above`'s closure): `eqEval
  (selectorPoint selector n) right` in X0, X1. The shifts are `lsr`: `min n |right| ≤ 64`.
- `multilinear_eval_by(n, |i| mle[i], point)` (X0; `mle` X1, X2; `point` X3, X4; `n = |mle|`,
  as `multilinear_eval` calls it): `multilinearEval mle point` in X0, X1. rustc dropped the
  `|point| ≥ 64` test (the levels index a 64-entry array): `|point| < 64`.
- `multilinear_eval_by(n, |i| EW::of_k(words[i]), point)` (`computed_bytecode_value`'s closure;
  X0; `words` X1, X2; `point` X3, X4; `n = |words|`): `multilinearEval (words.map EW.ofK) point`
  in X0, X1.
- `Buf<EW, N>::extend(self, xs)` (X0; X1, X2; `N ∈ {30, 36, 63, 230}`) and
  `Buf<u64, 230>::extend`: W0 = 1 (`Some`) and the buffer holds its entries then `xs` when they
  fit, else W0 = 0 (`None`, the buffer's bytes changed, as Rust's partial pushes leave them).
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model
open NativeRustcVm (ewsOf wordsOf wordOf bufEWOf bufWordsOf BufEWAt BufWordsAt EWsAt)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- `sum_e` uses no stack. -/
def sumEStack : Nat := 0
/-- The stack `prod_e` uses: its 32-byte frame, `EW::mul`'s included. -/
def prodEStack : Nat := 32 + ewMulStack
/-- The stack `dot` uses. -/
def dotStack : Nat := 48 + ewMulStack
/-- The stack `powers` uses. -/
def powersStack : Nat := 48 + ewMulStack
/-- The stack `eq_eval` uses. -/
def eqEvalStack : Nat := 32 + ewMulStack
/-- The stack `eq_kernel` uses. -/
def eqKernelStack : Nat := 112 + ewMulStack
/-- The stack `poly_eval` uses. -/
def polyEvalStack : Nat := 64 + ewMulStack
/-- The stack `index_mle_from` uses. -/
def indexMleFromStack : Nat := 64 + ewMulStack
/-- The stack `padding_weight` uses. -/
def paddingWeightStack : Nat := 112 + ewMulStack
/-- `selector_point` uses no stack. -/
def selectorPointStack : Nat := 0
/-- The stack `eq_eval_fn` uses. -/
def eqEvalFnStack : Nat := 48 + ewMulStack
/-- The stack `multilinear_eval_by` uses: 96 bytes of saved registers, 1136 of locals (the
pending entries and the `full` flags). -/
def mleStack : Nat := 1232 + ewMulStack
/-- `Buf::extend` uses no stack. -/
def bufExtendStack : Nat := 0

/-! ## Arguments -/

/-- An `E` element in two registers, limb `0` first. -/
def ewArg (lo hi : UInt64) : EW := ⟨lo, hi⟩

/-- The `E` element a function returns: X0, X1. -/
def ewRet (m : MachineData) : EW := ⟨m.regs.X0, m.regs.X1⟩

/-- The `n` bytes from `a` are data memory and do not wrap around. -/
def Readable (m : MachineData) (a : BitVec 64) (n : Nat) : Prop :=
  Mapped m.dmem a n ∧ NoWrap a n

/-- The `n` bytes from `a` are apart from the `s` bytes of stack below SP. -/
def OffStack (m : MachineData) (a : BitVec 64) (n s : Nat) : Prop :=
  Apart a n (stackBelow m s) s

/-- The elements of the slice (`a`, `n`): `n` elements of `E` from `a`. -/
def slice (m : MachineData) (a : UInt64) (n : UInt64) : Array EW :=
  (ewsOf m.dmem a.toBitVec n.toNat).toArray

/-- A readable slice of `n` elements of `E` from `a`, apart from the `s` bytes below SP. -/
def SliceOk (m : MachineData) (a n : UInt64) (s : Nat) : Prop :=
  Readable m a.toBitVec (16 * n.toNat) ∧ OffStack m a.toBitVec (16 * n.toNat) s

/-- Memory changes only in the `s` bytes below SP and the `n` bytes from `a`. -/
def Changes (m m' : MachineData) (s : Nat) (a : BitVec 64) (n : Nat) : Prop :=
  SameOutside m.dmem m'.dmem (fun p ↦ InRange a n p ∨ InRange (stackBelow m s) s p)

/-! ## Contracts -/

/-- `sum_e`'s precondition: at most `16` values. rustc specialised the unrolled body to its
callers' lengths (`mu`, `16` entries; `msg` tails, at most `4`): blocks of four up to `16`, then
the rest one by one from `len & 28`, which is wrong from length `20` on. -/
def SumEPre (m : MachineData) : Prop :=
  m.regs.X1.toNat ≤ 16 ∧ Readable m m.regs.X0.toBitVec (16 * m.regs.X1.toNat)

/-- `sum_e`'s postcondition. -/
def SumEPost (m m' : MachineData) : Prop :=
  ewRet m' = sumE (slice m m.regs.X0 m.regs.X1) ∧ Changes m m' sumEStack 0 0 ∧ Saved m m'

/-- `prod_e`'s precondition: `2 ≤ len ≤ 4`. -/
def ProdEPre (m : MachineData) : Prop :=
  StackOk m prodEStack ∧ 2 ≤ m.regs.X1.toNat ∧ m.regs.X1.toNat ≤ 4 ∧
    SliceOk m m.regs.X0 m.regs.X1 prodEStack

/-- `prod_e`'s postcondition. -/
def ProdEPost (m m' : MachineData) : Prop :=
  ewRet m' = prodE (slice m m.regs.X0 m.regs.X1) ∧ Changes m m' prodEStack 0 0 ∧ Saved m m'

/-- `dot`'s precondition. -/
def DotPre (m : MachineData) : Prop :=
  StackOk m dotStack ∧ SliceOk m m.regs.X0 m.regs.X1 dotStack ∧
    SliceOk m m.regs.X2 m.regs.X3 dotStack

/-- `dot`'s postcondition. -/
def DotPost (m m' : MachineData) : Prop :=
  ewRet m' = dot (slice m m.regs.X0 m.regs.X1) (slice m m.regs.X2 m.regs.X3) ∧
    Changes m m' dotStack 0 0 ∧ Saved m m'

/-- `powers`'s precondition. -/
def PowersPre (m : MachineData) : Prop :=
  StackOk m powersStack ∧ SliceOk m m.regs.X2 m.regs.X3 powersStack

/-- `powers`'s postcondition. -/
def PowersPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem m.regs.X2.toBitVec (powers (ewArg m.regs.X0 m.regs.X1) m.regs.X3.toNat).toList ∧
    Changes m m' powersStack m.regs.X2.toBitVec (16 * m.regs.X3.toNat) ∧ Saved m m'

/-- `eq_eval`'s precondition. -/
def EqEvalPre (m : MachineData) : Prop :=
  StackOk m eqEvalStack ∧ SliceOk m m.regs.X0 m.regs.X1 eqEvalStack ∧
    SliceOk m m.regs.X2 m.regs.X3 eqEvalStack

/-- `eq_eval`'s postcondition. -/
def EqEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = eqEval (slice m m.regs.X0 m.regs.X1) (slice m m.regs.X2 m.regs.X3) ∧
    Changes m m' eqEvalStack 0 0 ∧ Saved m m'

/-- `eq_kernel`'s precondition: `|point| < 64`, `out` apart from `point`. -/
def EqKernelPre (m : MachineData) : Prop :=
  StackOk m eqKernelStack ∧ m.regs.X1.toNat < 64 ∧ SliceOk m m.regs.X0 m.regs.X1 eqKernelStack ∧
    SliceOk m m.regs.X2 m.regs.X3 eqKernelStack ∧
    Apart m.regs.X0.toBitVec (16 * m.regs.X1.toNat) m.regs.X2.toBitVec (16 * m.regs.X3.toNat)

/-- `eq_kernel`'s postcondition. -/
def EqKernelPost (m m' : MachineData) : Prop :=
  (if 2 ^ m.regs.X1.toNat ≤ m.regs.X3.toNat then
      m'.regs.X0 = 1 ∧ m'.regs.X1.toNat = 2 ^ m.regs.X1.toNat ∧
        EWsAt m'.dmem m.regs.X2.toBitVec (eqKernel (slice m m.regs.X0 m.regs.X1)).toList
    else m'.regs.X0 = 0) ∧
    Changes m m' eqKernelStack m.regs.X2.toBitVec (16 * m.regs.X3.toNat) ∧ Saved m m'

/-- `poly_eval`'s precondition: at least one coefficient. -/
def PolyEvalPre (m : MachineData) : Prop :=
  StackOk m polyEvalStack ∧ 1 ≤ m.regs.X1.toNat ∧ SliceOk m m.regs.X0 m.regs.X1 polyEvalStack

/-- `poly_eval`'s postcondition. -/
def PolyEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = polyEval (slice m m.regs.X0 m.regs.X1) (ewArg m.regs.X2 m.regs.X3) ∧
    Changes m m' polyEvalStack 0 0 ∧ Saved m m'

/-- `index_mle_from`'s precondition. -/
def IndexMleFromPre (m : MachineData) : Prop :=
  StackOk m indexMleFromStack ∧ SliceOk m m.regs.X0 m.regs.X1 indexMleFromStack

/-- `index_mle_from`'s postcondition. -/
def IndexMleFromPost (m m' : MachineData) : Prop :=
  ewRet m' = indexMleFrom gen (slice m m.regs.X0 m.regs.X1) ∧
    Changes m m' indexMleFromStack 0 0 ∧ Saved m m'

/-- `padding_weight`'s precondition: `|point| < 64`. -/
def PaddingWeightPre (m : MachineData) : Prop :=
  StackOk m paddingWeightStack ∧ m.regs.X1.toNat < 64 ∧
    SliceOk m m.regs.X0 m.regs.X1 paddingWeightStack

/-- `padding_weight`'s postcondition. -/
def PaddingWeightPost (m m' : MachineData) : Prop :=
  ewRet m' = paddingWeight (slice m m.regs.X0 m.regs.X1) m.regs.X2.toNat ∧
    Changes m m' paddingWeightStack 0 0 ∧ Saved m m'

/-- `selector_point`'s precondition. -/
def SelectorPointPre (m : MachineData) : Prop :=
  Readable m m.regs.X1.toBitVec (16 * m.regs.X2.toNat)

/-- `selector_point`'s postcondition. -/
def SelectorPointPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem m.regs.X1.toBitVec (selectorPoint m.regs.X0.toNat m.regs.X2.toNat).toList ∧
    Changes m m' selectorPointStack m.regs.X1.toBitVec (16 * m.regs.X2.toNat) ∧ Saved m m'

/-- `eq_eval_fn` (`eq_above`'s closure)'s precondition: `min n |right| ≤ 64`. -/
def EqEvalFnOfEqAbovePre (m : MachineData) : Prop :=
  StackOk m eqEvalFnStack ∧ min m.regs.X0.toNat m.regs.X3.toNat ≤ 64 ∧
    SliceOk m m.regs.X2 m.regs.X3 eqEvalFnStack

/-- `eq_eval_fn` (`eq_above`'s closure)'s postcondition. -/
def EqEvalFnOfEqAbovePost (m m' : MachineData) : Prop :=
  ewRet m' = eqEval (selectorPoint m.regs.X1.toNat m.regs.X0.toNat) (slice m m.regs.X2 m.regs.X3) ∧
    Changes m m' eqEvalFnStack 0 0 ∧ Saved m m'

/-- `multilinear_eval_by` (`multilinear_eval`'s closure)'s precondition: `n = |mle|`,
`|point| < 64`. -/
def MleOfMultilinearEvalPre (m : MachineData) : Prop :=
  StackOk m mleStack ∧ m.regs.X0 = m.regs.X2 ∧ m.regs.X4.toNat < 64 ∧
    SliceOk m m.regs.X1 m.regs.X2 mleStack ∧ SliceOk m m.regs.X3 m.regs.X4 mleStack

/-- `multilinear_eval_by` (`multilinear_eval`'s closure)'s postcondition. -/
def MleOfMultilinearEvalPost (m m' : MachineData) : Prop :=
  ewRet m' = multilinearEval (slice m m.regs.X1 m.regs.X2) (slice m m.regs.X3 m.regs.X4) ∧
    Changes m m' mleStack 0 0 ∧ Saved m m'

/-- The words of the slice (`a`, `n`), each an `E` element in limb `0`. -/
def wordSliceE (m : MachineData) (a n : UInt64) : Array EW :=
  ((wordsOf m.dmem a.toBitVec n.toNat).map EW.ofK).toArray

/-- `multilinear_eval_by` (`computed_bytecode_value`'s closure)'s precondition: `n = |words|`; the
words apart from the stack when there are any (an empty slice's pointer may dangle). -/
def MleOfComputedBytecodeValuePre (m : MachineData) : Prop :=
  StackOk m mleStack ∧ m.regs.X0 = m.regs.X2 ∧
    Readable m m.regs.X1.toBitVec (8 * m.regs.X2.toNat) ∧
    (0 < m.regs.X2.toNat → OffStack m m.regs.X1.toBitVec (8 * m.regs.X2.toNat) mleStack) ∧
    SliceOk m m.regs.X3 m.regs.X4 mleStack

/-- `multilinear_eval_by` (`computed_bytecode_value`'s closure)'s postcondition. -/
def MleOfComputedBytecodeValuePost (m m' : MachineData) : Prop :=
  ewRet m' = multilinearEval (wordSliceE m m.regs.X1 m.regs.X2) (slice m m.regs.X3 m.regs.X4) ∧
    Changes m m' mleStack 0 0 ∧ Saved m m'

/-- `Buf<EW, N>::extend`'s precondition: a valid buffer (count at most `N`) at X0, the slice
(X1, X2) apart from it. -/
def BufEWExtendPre (N : Nat) (m : MachineData) : Prop :=
  (wordOf m.dmem m.regs.X0.toBitVec).toNat ≤ N ∧ Readable m m.regs.X0.toBitVec (8 + 16 * N) ∧
    Readable m m.regs.X1.toBitVec (16 * m.regs.X2.toNat) ∧
    Apart m.regs.X0.toBitVec (8 + 16 * N) m.regs.X1.toBitVec (16 * m.regs.X2.toNat)

/-- `Buf<EW, N>::extend`'s postcondition. -/
def BufEWExtendPost (N : Nat) (m m' : MachineData) : Prop :=
  (if (wordOf m.dmem m.regs.X0.toBitVec).toNat + m.regs.X2.toNat ≤ N then
      m'.regs.X0 = 1 ∧ BufEWAt m'.dmem m.regs.X0.toBitVec N
        (bufEWOf m.dmem m.regs.X0.toBitVec ++ (slice m m.regs.X1 m.regs.X2).toList)
    else m'.regs.X0 = 0) ∧
    Changes m m' bufExtendStack m.regs.X0.toBitVec (8 + 16 * N) ∧ Saved m m'

/-- `Buf<u64, 230>::extend`'s precondition. -/
def BufU64ExtendPre (N : Nat) (m : MachineData) : Prop :=
  (wordOf m.dmem m.regs.X0.toBitVec).toNat ≤ N ∧ Readable m m.regs.X0.toBitVec (8 + 8 * N) ∧
    Readable m m.regs.X1.toBitVec (8 * m.regs.X2.toNat) ∧
    Apart m.regs.X0.toBitVec (8 + 8 * N) m.regs.X1.toBitVec (8 * m.regs.X2.toNat)

/-- `Buf<u64, 230>::extend`'s postcondition. -/
def BufU64ExtendPost (N : Nat) (m m' : MachineData) : Prop :=
  (if (wordOf m.dmem m.regs.X0.toBitVec).toNat + m.regs.X2.toNat ≤ N then
      m'.regs.X0 = 1 ∧ BufWordsAt m'.dmem m.regs.X0.toBitVec N
        (bufWordsOf m.dmem m.regs.X0.toBitVec ++
          wordsOf m.dmem m.regs.X1.toBitVec m.regs.X2.toNat)
    else m'.regs.X0 = 0) ∧
    Changes m m' bufExtendStack m.regs.X0.toBitVec (8 + 8 * N) ∧ Saved m m'

end

end NativeRustcVmArm
