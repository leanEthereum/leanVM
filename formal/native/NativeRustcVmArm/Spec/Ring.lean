module

public import NativeRustcVmArm.Code.Vm.ColumnWeight.Names
public import NativeRustcVmArm.Code.Vm.RingClaimWeight.Names
public import NativeRustcVmArm.Code.Vm.RingCoefficients.Names
public import NativeRustcVmArm.Code.Vm.RingPsi.Names
public import NativeRustcVmArm.Code.Vm.RingSwitch.Names
public import NativeRustcVmArm.Code.Vm.RingTarget.Names
public import NativeRustcVmArm.Code.Vm.RingWeight.Names
public import NativeRustcVmArm.Spec.Transcript
public import NativeRustcVmArm.Spec.Arrays
public import NativeRustcVm.Ring.Rep
public import NativeVm.Model.Claims

/-!
# The contracts of ring switching and the stack weights on AArch64

`ring_switch.rs`'s functions and `stack.rs`'s weights (`StackWeight.eval`). Each function uses the
stack below SP (`<fn>Stack` bytes, its callees' included; `StackOk` in its precondition) and
returns with the callee-saved registers and SP kept (`Saved`), no byte changed outside its outputs
and that stack. A slice of `E` is a pointer and a length in two registers (`slice`, `SliceOk`);
rustc fixed the lengths of the arrays (`f`, `g`: `8`; `s`, the coefficients: `64`) and passes
only their pointers. An `Option<EW>` result is the 24 bytes at the `sret` pointer X0 (`OptEWAt`).
The results are the model's (`NativeVm.Model`):

- `ring_psi(value, g)` (`value` X0, X1; `g` X2): `ringPsi value g` in X0, X1.
- `ring_coefficients(f, g, out)` (X0, X1, X2): the 64 elements at `out` become
  `ringCoefficients f g`.
- `ring_target(s, f, g)` (X0, X1, X2): `ringTarget s f g` in X0, X1.
- `ring_switch(t, s, out)` (X0, X1, X2): `ringSwitch point s` (the point passes through): X0 the
  `Option<()>`, and on `some` the `RingW` at `out` holds the target and the coefficients
  (`NativeRustcVm.Ring.RingWAt`), the `TState` the next state.
- `ring_weight(out, r, r', coefficients)` (X0; X1, X2; X3, X4; X5): `some (ringWeight r r'
  coefficients)`. rustc dropped the Rust's test `|r| ≤ pointCap` (its only caller passes
  `KeccakOutW`'s point, a `Buf<EW, 36>`): `|r| ≤ 36`.
- `ring_claim_weight(out, p, r, coefficients, x)` (X0; `p` X1, X2; `r` X3, X4; X5; `x` X6, X7):
  `some (StackWeight.eval (.ring p r coefficients) x)`; `|r| ≤ 36` and `|x| ≤ 64` (the shifts of
  `eq_above` are `lsr`; `x` is a point on the stack, `stackLog ≤ 30`).
- `column_weight(out, p, point, stack_log, x)` (X0; `p` X1, X2; `point` X3, X4; X5; `x` X6, X7):
  `StackWeight.eval (.eq (stackPoint p point stackLog)) x` when the stack point fits its
  `pointCap + stackCap = 66` slots, else `none`.
-/

namespace NativeRustcVmArm

open NativeRustcArm NativeVm.Model NativeRustcVm.Transcript NativeRustcVm.Ring
open LeanVM.Protocol.Verifier (Placement)

@[expose] public section

/-! ## Symbols -/


/-! ## Stacks -/

/-- The stack `ring_psi` uses: its 48-byte frame, `EW::mul`'s included. -/
def ringPsiStack : Nat := 48 + ewMulStack
/-- The stack `ring_coefficients` uses: its 176-byte frame, `EW::sq_iter`'s (above `EW::mul`'s)
included. -/
def ringCoefficientsStack : Nat := 176 + ewSqIterStack
/-- The stack `ring_target` uses: 96 bytes of saved registers, 2256 of locals (the images twice,
the products), `poly_eval`'s included (the largest of its callees': `ring_psi`, `memcpy`,
`EW::sq_iter`, `EW::mul`). -/
def ringTargetStack : Nat := 2352 + polyEvalStack
/-- The stack `ring_switch` uses: its 432-byte frame (the challenges, `g`), `ring_target`'s
included (the largest of its callees': `grind`, `sample_challenges`, `ring_coefficients`). -/
def ringSwitchStack : Nat := 432 + ringTargetStack
/-- The stack `ring_weight` uses: 96 bytes of saved registers, 592 of locals (the powers),
`EW::mul`'s included. -/
def ringWeightStack : Nat := 688 + ewMulStack
/-- The stack `ring_claim_weight` uses: its 112-byte frame, `ring_weight`'s included (above
`eq_eval_fn`'s). -/
def ringClaimWeightStack : Nat := 112 + ringWeightStack
/-- The stack `column_weight` uses: 48 bytes of saved registers, 1056 of locals (the stack
point's 66 slots), `eq_eval`'s included (above `stack_point`'s). -/
def columnWeightStack : Nat := 1104 + eqEvalStack

/-! ## Arguments -/

/-- `RING_MAP_WIDTH`: `f`'s and `g`'s length. -/
def ringWidth : Nat := 8

/-- The `n` elements of `E` from `a` (an array rustc passes by its pointer only). -/
def arr (m : MachineData) (a : UInt64) (n : Nat) : Array EW :=
  (NativeRustcVm.ewsOf m.dmem a.toBitVec n).toArray

/-- A readable array of `n` elements of `E` from `a`, apart from the `s` bytes below SP. -/
def ArrOk (m : MachineData) (a : UInt64) (n s : Nat) : Prop :=
  Readable m a.toBitVec (16 * n) ∧ OffStack m a.toBitVec (16 * n) s

/-- An `Option<EW>` output (24 bytes) at `o`: readable and apart from the `s` bytes below SP. -/
def OptOutOk (m : MachineData) (o : UInt64) (s : Nat) : Prop :=
  Readable m o.toBitVec 24 ∧ OffStack m o.toBitVec 24 s

/-- The placement `p` in X1 (`variable_count`), X2 (`index`). -/
def placementArg (m : MachineData) : Placement := ⟨m.regs.X1.toNat, m.regs.X2.toNat⟩

/-! ## `ring_switch.rs` -/

/-- `ring_psi`'s precondition: `g`'s 8 elements at X2. -/
def RingPsiPre (m : MachineData) : Prop :=
  StackOk m ringPsiStack ∧ ArrOk m m.regs.X2 ringWidth ringPsiStack

/-- `ring_psi`'s postcondition. -/
def RingPsiPost (m m' : MachineData) : Prop :=
  ewRet m' = ringPsi (ewArg m.regs.X0 m.regs.X1) (arr m m.regs.X2 ringWidth) ∧
    Changes m m' ringPsiStack 0 0 ∧ Saved m m'

/-- `ring_coefficients`'s precondition: `f` (X0) and `g` (X1), 8 elements each, `out` (X2) 64,
apart from them. -/
def RingCoefficientsPre (m : MachineData) : Prop :=
  StackOk m ringCoefficientsStack ∧ ArrOk m m.regs.X0 ringWidth ringCoefficientsStack ∧
    ArrOk m m.regs.X1 ringWidth ringCoefficientsStack ∧
    ArrOk m m.regs.X2 coeffCount ringCoefficientsStack ∧
    Apart m.regs.X2.toBitVec (16 * coeffCount) m.regs.X0.toBitVec (16 * ringWidth) ∧
    Apart m.regs.X2.toBitVec (16 * coeffCount) m.regs.X1.toBitVec (16 * ringWidth)

/-- `ring_coefficients`'s postcondition. -/
def RingCoefficientsPost (m m' : MachineData) : Prop :=
  NativeRustcVm.EWsAt m'.dmem m.regs.X2.toBitVec
      (ringCoefficients (arr m m.regs.X0 ringWidth) (arr m m.regs.X1 ringWidth)).toList ∧
    Changes m m' ringCoefficientsStack m.regs.X2.toBitVec (16 * coeffCount) ∧ Saved m m'

/-- `ring_target`'s precondition: `s` (X0, 64 elements), `f` (X1) and `g` (X2), 8 each. -/
def RingTargetPre (m : MachineData) : Prop :=
  StackOk m ringTargetStack ∧ ArrOk m m.regs.X0 coeffCount ringTargetStack ∧
    ArrOk m m.regs.X1 ringWidth ringTargetStack ∧ ArrOk m m.regs.X2 ringWidth ringTargetStack

/-- `ring_target`'s postcondition. -/
def RingTargetPost (m m' : MachineData) : Prop :=
  ewRet m' = ringTarget (arr m m.regs.X0 coeffCount) (arr m m.regs.X1 ringWidth)
      (arr m m.regs.X2 ringWidth) ∧
    Changes m m' ringTargetStack 0 0 ∧ Saved m m'

section
variable [Labels]

/-- `ring_switch`'s precondition: the `TState` at X0 represents `s`; `s`'s 64 slices at X1,
apart from the `TState` and from the `RingW` at X2 (`OutOk`). -/
def RingSwitchPre (a : DecArea) (s : TState) (m : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let sl := m.regs.X1.toBitVec; let o := m.regs.X2.toBitVec
  StackOk m ringSwitchStack ∧ RcAt m ringSwitchStack ∧ TStateAt m.dmem t a s ∧
    TStateOk m t a ringSwitchStack ∧ OutOk m t a o ringWBytes ringSwitchStack ∧
    ArrOk m m.regs.X1 coeffCount ringSwitchStack ∧ Apart sl (16 * coeffCount) t tstateBytes ∧
    Apart sl (16 * coeffCount) o ringWBytes

/-- `ring_switch`'s postcondition, for any point the model passes through. -/
def RingSwitchPost (a : DecArea) (s : TState) (point : Array EW) (m m' : MachineData) : Prop :=
  let t := m.regs.X0.toBitVec; let o := m.regs.X2.toBitVec
  let r := (ringSwitch point (arr m m.regs.X1 coeffCount)).run s
  m'.regs.X0 = okWord r.isSome ∧
    (∀ x s', r = some (x, s') → RingWAt m'.dmem o x.1 x.2.2 ∧ TStateAt m'.dmem t a s') ∧
    SameOutside m.dmem m'.dmem (fun q ↦ InRange o ringWBytes q ∨ InRange t tstateBytes q ∨
      InRange (stackBelow m ringSwitchStack) ringSwitchStack q) ∧ Saved m m'

end

/-! ## `stack.rs`'s weights -/

/-- `ring_weight`'s precondition: `r` (X1, X2; at most `36`), `r'` (X3, X4), the 64
coefficients (X5), the `Option<EW>` at X0. -/
def RingWeightPre (m : MachineData) : Prop :=
  StackOk m ringWeightStack ∧ m.regs.X2.toNat ≤ 36 ∧
    SliceOk m m.regs.X1 m.regs.X2 ringWeightStack ∧
    SliceOk m m.regs.X3 m.regs.X4 ringWeightStack ∧
    ArrOk m m.regs.X5 coeffCount ringWeightStack ∧ OptOutOk m m.regs.X0 ringWeightStack

/-- `ring_weight`'s postcondition. -/
def RingWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem m.regs.X0.toBitVec (some (ringWeight (slice m m.regs.X1 m.regs.X2)
      (slice m m.regs.X3 m.regs.X4) (arr m m.regs.X5 coeffCount))) ∧
    Changes m m' ringWeightStack m.regs.X0.toBitVec 24 ∧ Saved m m'

/-- `ring_claim_weight`'s precondition: `r` (X3, X4; at most `36`), the 64 coefficients (X5),
`x` (X6, X7; at most `64`), the `Option<EW>` at X0. -/
def RingClaimWeightPre (m : MachineData) : Prop :=
  StackOk m ringClaimWeightStack ∧ m.regs.X4.toNat ≤ 36 ∧ m.regs.X7.toNat ≤ 64 ∧
    SliceOk m m.regs.X3 m.regs.X4 ringClaimWeightStack ∧
    ArrOk m m.regs.X5 coeffCount ringClaimWeightStack ∧
    SliceOk m m.regs.X6 m.regs.X7 ringClaimWeightStack ∧
    OptOutOk m m.regs.X0 ringClaimWeightStack

/-- `ring_claim_weight`'s postcondition. -/
def RingClaimWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem m.regs.X0.toBitVec (some (StackWeight.eval
      (.ring (placementArg m) (slice m m.regs.X3 m.regs.X4) (arr m m.regs.X5 coeffCount))
      (slice m m.regs.X6 m.regs.X7))) ∧
    Changes m m' ringClaimWeightStack m.regs.X0.toBitVec 24 ∧ Saved m m'

/-- `column_weight`'s precondition: `point` (X3, X4; fewer than `64`, as `stack_point` needs), `x`
(X6, X7), the `Option<EW>` at X0. -/
def ColumnWeightPre (m : MachineData) : Prop :=
  StackOk m columnWeightStack ∧ SliceOk m m.regs.X3 m.regs.X4 columnWeightStack ∧
    SliceOk m m.regs.X6 m.regs.X7 columnWeightStack ∧ OptOutOk m m.regs.X0 columnWeightStack ∧
    m.regs.X4.toNat < 64

/-- `column_weight`'s postcondition: `none` when the stack point does not fit its 66 slots. -/
def ColumnWeightPost (m m' : MachineData) : Prop :=
  OptEWAt m'.dmem m.regs.X0.toBitVec
      (if m.regs.X4.toNat + (m.regs.X5.toNat - m.regs.X1.toNat) ≤ 66 then
        some (StackWeight.eval (.eq (stackPoint (placementArg m) (slice m m.regs.X3 m.regs.X4)
          m.regs.X5.toNat)) (slice m m.regs.X6 m.regs.X7))
      else none) ∧
    Changes m m' columnWeightStack m.regs.X0.toBitVec 24 ∧ Saved m m'

end

end NativeRustcVmArm
