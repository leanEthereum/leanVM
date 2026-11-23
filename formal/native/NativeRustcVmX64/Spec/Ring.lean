module

public import NativeRustcVmX64.Spec.Transcript
public import NativeRustcVmX64.Spec.Arrays
public import NativeRustcX64.Spec.Got
public import NativeRustcVm.Ring.Rep
public import NativeVm.Model.Claims
public import NativeRustcVmX64.Code.Vm.ColumnWeight.Names
public import NativeRustcVmX64.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmX64.Code.Vm.RingCoefficients.Names
public import NativeRustcVmX64.Code.Vm.RingPsi.Names
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public import NativeRustcVmX64.Code.Vm.RingTarget.Names
public import NativeRustcVmX64.Code.Vm.RingWeight.Names
public import NativeRustcVmX64.Code.Vm.StackPoint.Names

/-!
# The contracts of ring switching and the stack weights on x86-64

The AArch64 contracts (`NativeRustcVmArm.Spec.Ring`) with the System V registers: arguments in
RDI, RSI, RDX, RCX, R8, R9, then on the stack above the return address (`stackArg`, mapped by
`ArgsOk`); an `E` result in RAX, RDX; an `Option<()>` in AL (`OkAl`); an `Option<EW>` result the
24 bytes at the `sret` pointer RDI (`OptEWAt`). Each function uses the stack below RSP
(`<fn>Stack` bytes: its pushes, its frame, its callees' return addresses and stacks; `StackOk` also
maps its return address at RSP) and returns with the callee-saved registers kept (and RSP 8 above,
`Spec`), no byte changed outside its outputs and that stack. rustc fixed the lengths of the arrays
(`f`, `g`: `8`; `s`, the coefficients: `64`) and passes only their pointers. The results are the
model's (`NativeVm.Model`):

- `ring_psi(value, g)` (`value` RDI, RSI; `g` RDX): `ringPsi value g` in RAX, RDX.
- `ring_coefficients(f, g, out)` (RDI, RSI, RDX): the 64 elements at `out` become
  `ringCoefficients f g`.
- `ring_target(s, f, g)` (RDI, RSI, RDX): `ringTarget s f g` in RAX, RDX.
- `ring_switch(t, s, out)` (RDI, RSI, RDX): `ringSwitch point s` (the point passes through): AL the
  `Option<()>`, and on `some` the `RingW` at `out` holds the target and the coefficients
  (`NativeRustcVm.Ring.RingWAt`), the `TState` the next state.
- `ring_weight(out, r, r', coefficients)` (RDI; RSI, RDX; RCX, R8; R9): `some (ringWeight r r'
  coefficients)`, for `|r| ≤ 36` (AArch64's bound: its only caller passes `KeccakOutW`'s point).
- `ring_claim_weight(out, p, r, coefficients, x)` (RDI; `p` RSI, RDX; `r` RCX, R8; R9; `x` the two
  words on the stack): `some (StackWeight.eval (.ring p r coefficients) x)`, for `|r| ≤ 36` and
  `|x| ≤ 64` (AArch64's bounds).
- `column_weight(out, p, point, stack_log, x)` (RDI; `p` RSI, RDX; `point` RCX, R8; R9; `x` the two
  words on the stack): `StackWeight.eval (.eq (stackPoint p point stackLog)) x` when the stack
  point fits its `pointCap + stackCap = 66` slots, else `none`; `|point| < 64`.
- `stack_point(p, point, stack_log, out)` (`p` RDI, RSI; `point` RDX, RCX; R8; R9, rustc fixed `out`'s
  length to `66`), `column_weight`'s callee: `stackPoint` at `out`, RAX = 1 and its length in RDX,
  or RAX = 0 (`None`) when longer than `66`; `|point| < 64` (the pair-copy loop's `and $62`). Its
  contract belongs with the layout's; it is stated here until the x86-64 layout area has one.
-/

namespace NativeRustcVmX64

open NativeRustcX64 NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Ring
open NativeRustcVm (ewsOf EWsAt)
open LeanVM.Protocol.Verifier (Placement)

@[expose] public section

/-! ## Stacks -/

/-- The stack `ring_psi` uses: 6 pushes, its 24-byte frame, `EW::mul`'s return address and
stack. -/
def ringPsiStack : Nat := 80 + ewMulStack
/-- The stack `ring_coefficients` uses: 6 pushes, its 120-byte frame, the return address and stack
of `EW::sq_iter` (the larger of its callees', above `EW::mul`'s). -/
def ringCoefficientsStack : Nat := 176 + ewSqIterStack
/-- The stack `ring_target` uses: 6 pushes, its 2296-byte frame (the images twice, the
products), the return address and stack of `ring_psi` (the largest of its callees': `poly_eval`,
`memcpy`, `EW::sq_iter`, `EW::mul`). -/
def ringTargetStack : Nat := 2352 + ringPsiStack
/-- The stack `ring_switch` uses: 5 pushes, its 384-byte frame (the challenges, `g`), the return
address and stack of `ring_target` (the largest of its callees': `grind`, `sample_challenges`,
`ring_coefficients`). -/
def ringSwitchStack : Nat := 432 + ringTargetStack
/-- The stack `ring_weight` uses: 6 pushes, its 616-byte frame (the powers), `EW::mul`'s return
address and stack. -/
def ringWeightStack : Nat := 672 + ewMulStack
/-- The stack `ring_claim_weight` uses: 6 pushes, its 40-byte frame (`ring_weight`'s output), the
return address and stack of `ring_weight` (above `eq_eval_fn`'s and `EW::mul`'s). -/
def ringClaimWeightStack : Nat := 96 + ringWeightStack
/-- The stack `stack_point` uses: 5 pushes, `selector_point`'s return address and stack. -/
def stackPointStack : Nat := 48 + selectorPointStack
/-- The stack `column_weight` uses: 3 pushes, its 1056-byte frame (the stack point's 66 slots),
the return address and stack of `eq_eval` (above `stack_point`'s). -/
def columnWeightStack : Nat := 1088 + eqEvalStack

/-! ## Arguments -/

/-- `RING_MAP_WIDTH`: `f`'s and `g`'s length. -/
def ringWidth : Nat := 8

/-- `stack_point`'s output: `66` elements of `E`. -/
def stackPointOut : Nat := 66

/-- The `n` elements of `E` from `a` (an array rustc passes by its pointer only). -/
def arr (m : MachineData) (a : BitVec 64) (n : Nat) : Array EW := (ewsOf m.dmem a n).toArray

/-- A readable array of `n` elements of `E` from `a`, apart from the `s` bytes below RSP and the
return address. -/
def ArrOk (m : MachineData) (a : BitVec 64) (n s : Nat) : Prop :=
  Readable m a (16 * n) ∧ OffStack m a (16 * n) s

/-- An `Option<EW>` output (24 bytes) at `o`: readable, apart from the `s` bytes below RSP, the
return address and the `k` argument words above it. -/
def OptOutOk (m : MachineData) (o : BitVec 64) (s k : Nat) : Prop :=
  Readable m o 24 ∧ OffStack m o 24 s ∧ Apart o 24 (rspOf m + 8#64) (8 * k)

/-- The placement `p` in RSI (`variable_count`), RDX (`index`). -/
def placementArg (m : MachineData) : Placement := ⟨(reg m .rsi).toNat, (reg m .rdx).toNat⟩

/-! ## `ring_switch.rs` -/

/-- `ring_psi`'s precondition: `g`'s 8 elements at RDX. -/
def RingPsiPre (m : MachineData) : Prop :=
  StackOk m ringPsiStack ∧ ArrOk m (reg m .rdx) ringWidth ringPsiStack

/-- `ring_psi`'s postcondition. -/
def RingPsiPost (m m' : MachineData) : Prop :=
  ewRet m' = ringPsi (ewArg (reg m .rdi) (reg m .rsi)) (arr m (reg m .rdx) ringWidth) ∧
    Changes m m' ringPsiStack 0 0 ∧ Saved m m'

/-- `ring_coefficients`'s precondition: `f` (RDI) and `g` (RSI), 8 elements each, `out` (RDX) 64,
apart from them. -/
def RingCoefficientsPre (m : MachineData) : Prop :=
  StackOk m ringCoefficientsStack ∧ ArrOk m (reg m .rdi) ringWidth ringCoefficientsStack ∧
    ArrOk m (reg m .rsi) ringWidth ringCoefficientsStack ∧
    ArrOk m (reg m .rdx) coeffCount ringCoefficientsStack ∧
    Apart (reg m .rdx) (16 * coeffCount) (reg m .rdi) (16 * ringWidth) ∧
    Apart (reg m .rdx) (16 * coeffCount) (reg m .rsi) (16 * ringWidth)

/-- `ring_coefficients`'s postcondition. -/
def RingCoefficientsPost (m m' : MachineData) : Prop :=
  EWsAt m'.dmem (reg m .rdx)
      (ringCoefficients (arr m (reg m .rdi) ringWidth) (arr m (reg m .rsi) ringWidth)).toList ∧
    Changes m m' ringCoefficientsStack (reg m .rdx) (16 * coeffCount) ∧ Saved m m'

/-- `ring_target`'s precondition: `s` (RDI, 64 elements), `f` (RSI) and `g` (RDX), 8 each,
and the read-only `memcpy` GOT slot. -/
def RingTargetPre [Labels] (m : MachineData) : Prop :=
  StackOk m ringTargetStack ∧ ArrOk m (reg m .rdi) coeffCount ringTargetStack ∧
    ArrOk m (reg m .rsi) ringWidth ringTargetStack ∧ ArrOk m (reg m .rdx) ringWidth ringTargetStack ∧
    GotAt m ringTargetStack [(reg m .rdi, 16 * coeffCount),
      (reg m .rsi, 16 * ringWidth), (reg m .rdx, 16 * ringWidth)] ["memcpy"]

/-- `ring_target`'s postcondition. -/
def RingTargetPost (m m' : MachineData) : Prop :=
  ewRet m' = ringTarget (arr m (reg m .rdi) coeffCount) (arr m (reg m .rsi) ringWidth)
      (arr m (reg m .rdx) ringWidth) ∧
    Changes m m' ringTargetStack 0 0 ∧ Saved m m'

section
variable [Labels]

/-- `ring_switch`'s precondition: the `TState` at RDI represents `s`; `s`'s 64 slices at RSI,
apart from the `TState` and from the `RingW` at RDX (`OutOk`). -/
def RingSwitchPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := reg m .rdi; let sl := reg m .rsi; let o := reg m .rdx
  StackOk m ringSwitchStack ∧ RcAt m ringSwitchStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a ringSwitchStack ∧ OutOk m t a o ringWBytes ringSwitchStack ∧
    ArrOk m sl coeffCount ringSwitchStack ∧ Apart sl (16 * coeffCount) t tstateBytes ∧
    Apart sl (16 * coeffCount) o ringWBytes ∧
    GotAt m ringSwitchStack [(t, tstateBytes), (a.words, 8 * a.len), (o, ringWBytes),
      (sl, 16 * coeffCount), (rcAddr, 192)] ["memcpy"]

/-- `ring_switch`'s postcondition, for any point the model passes through. -/
def RingSwitchPost (a : DecArea) (s : TState) (point : Array EW) (m m' : MachineData) : Prop :=
  let t := reg m .rdi; let o := reg m .rdx
  let r := (ringSwitch point (arr m (reg m .rsi) coeffCount)).run s
  OkAl m' r.isSome ∧
    (∀ x s', r = some (x, s') → RingWAt m'.dmem o x.1 x.2.2 ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o ringWBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m ringSwitchStack) ringSwitchStack q) ∧ Saved m m'

end

/-! ## `stack.rs`'s weights -/

/-- `ring_weight`'s precondition: `r` (RSI, RDX; at most `36`), `r'` (RCX, R8), the 64
coefficients (R9), the `Option<EW>` at RDI. -/
def RingWeightPre (m : MachineData) : Prop :=
  StackOk m ringWeightStack ∧ (reg m .rdx).toNat ≤ 36 ∧
    SliceOk m (reg m .rsi) (reg m .rdx) ringWeightStack ∧
    SliceOk m (reg m .rcx) (reg m .r8) ringWeightStack ∧
    ArrOk m (reg m .r9) coeffCount ringWeightStack ∧ OptOutOk m (reg m .rdi) ringWeightStack 0

/-- `ring_weight`'s postcondition. -/
def RingWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem (reg m .rdi) (some (ringWeight (slice m (reg m .rsi) (reg m .rdx))
      (slice m (reg m .rcx) (reg m .r8)) (arr m (reg m .r9) coeffCount))) ∧
    Changes m m' ringWeightStack (reg m .rdi) 24 ∧ Saved m m'

/-- `ring_claim_weight`'s precondition: `r` (RCX, R8; at most `36`), the 64 coefficients (R9),
`x` (stack words `0`, `1`; at most `64`), the `Option<EW>` at RDI. -/
def RingClaimWeightPre (m : MachineData) : Prop :=
  StackOk m ringClaimWeightStack ∧ ArgsOk m 2 ∧ (reg m .r8).toNat ≤ 36 ∧
    (stackArg m 1).toNat ≤ 64 ∧ SliceOk m (reg m .rcx) (reg m .r8) ringClaimWeightStack ∧
    ArrOk m (reg m .r9) coeffCount ringClaimWeightStack ∧
    SliceOk m (stackArg m 0) (stackArg m 1) ringClaimWeightStack ∧
    OptOutOk m (reg m .rdi) ringClaimWeightStack 2

/-- `ring_claim_weight`'s postcondition. -/
def RingClaimWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem (reg m .rdi) (some (StackWeight.eval
      (.ring (placementArg m) (slice m (reg m .rcx) (reg m .r8)) (arr m (reg m .r9) coeffCount))
      (slice m (stackArg m 0) (stackArg m 1)))) ∧
    Changes m m' ringClaimWeightStack (reg m .rdi) 24 ∧ Saved m m'

/-- `stack_point`'s precondition: the point (RDX, RCX; fewer than `64` coordinates), the output's
`66` elements at R9. -/
def StackPointPre (m : MachineData) : Prop :=
  let o := reg m .r9; let n := 16 * stackPointOut
  StackOk m stackPointStack ∧ SliceOk m (reg m .rdx) (reg m .rcx) stackPointStack ∧
    Readable m o n ∧ OffStack m o n stackPointStack ∧
    Apart o n (reg m .rdx) (16 * (reg m .rcx).toNat) ∧ (reg m .rcx).toNat < 64

/-- `stack_point`'s postcondition. -/
def StackPointPost (m m' : MachineData) : Prop :=
  let o := reg m .r9; let n := (reg m .rcx).toNat + ((reg m .r8).toNat - (reg m .rdi).toNat)
  (if n ≤ stackPointOut then
      reg m' .rax = 1#64 ∧ (reg m' .rdx).toNat = n ∧
        EWsAt m'.dmem o (stackPoint ⟨(reg m .rdi).toNat, (reg m .rsi).toNat⟩
          (slice m (reg m .rdx) (reg m .rcx)) (reg m .r8).toNat).toList
    else reg m' .rax = 0#64) ∧
    Changes m m' stackPointStack o (16 * stackPointOut) ∧ Saved m m'

/-- `column_weight`'s precondition: `point` (RCX, R8; fewer than `64`, as `stack_point` needs),
`x` (stack words `0`, `1`), the `Option<EW>` at RDI. -/
def ColumnWeightPre (m : MachineData) : Prop :=
  StackOk m columnWeightStack ∧ ArgsOk m 2 ∧ SliceOk m (reg m .rcx) (reg m .r8) columnWeightStack ∧
    SliceOk m (stackArg m 0) (stackArg m 1) columnWeightStack ∧
    OptOutOk m (reg m .rdi) columnWeightStack 2 ∧ (reg m .r8).toNat < 64

/-- `column_weight`'s postcondition: `none` when the stack point does not fit its 66 slots. -/
def ColumnWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem (reg m .rdi)
      (if (reg m .r8).toNat + ((reg m .r9).toNat - (reg m .rsi).toNat) ≤ stackPointOut then
        some (StackWeight.eval (.eq (stackPoint (placementArg m) (slice m (reg m .rcx) (reg m .r8))
          (reg m .r9).toNat)) (slice m (stackArg m 0) (stackArg m 1)))
      else none) ∧
    Changes m m' columnWeightStack (reg m .rdi) 24 ∧ Saved m m'

end

end NativeRustcVmX64
