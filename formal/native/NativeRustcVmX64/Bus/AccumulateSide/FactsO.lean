module

public import NativeRustcVmX64.Bus.AccumulateSide.FactsK
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public meta import NativeRustcVmX64.Bus.AccumulateSide.Exec

/-!
# `accumulate_side`: the framework ones' blocks (x86-64)

What the executor's summaries say of `b6` to `b12`, checked by the kernel.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.AccumulateSide NativeRustcVmX64.Transcript

@[expose] public section

/-- `b6`'s exit: no framework block. -/
def c6 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .r13) (.reg .r13)) (.lit 0)

/-- `eq_above`'s arguments in `b8`. -/
def satO : Sym := .ite (.cmp .ult .W64 (.reg .rbp) (.load 1 0 8)) (.reg .rbx)
  (.bin .sub .W64 (.reg .rbp) (.load 1 0 8))
def shrO : Sym := .ite (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 64))) (.reg .rbx)
  (.bin .shr .W64 (.load 1 8 8) (.load 1 0 8))
def aboveO : Sym := .ite (.cmp .ult .W64 (.reg .rbp) (.load 1 0 8)) (.lit 8)
  (.bin .add .W64 (.reg .rdi) (.bin .shl .W64 (.load 1 0 8) (.lit 4)))

/-- `b9`'s exit: more framework blocks. -/
def c9 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .r12)) (.reg .r13))

end

public theorem exit_b6 : exec b6 fS = some (after b6 fS, .cond c6 NativeRustcVmX64.Vm.AccumulateSide.label_5) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : MidOk F 8 slots (after b6 fS) = true ∧
    (after b6 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b6 fS) D6 D6 = true := by
  rw [after_eq run_b6]; decide +kernel

public theorem exit_b7 : exec b7 fS = some (after b7 fS, .fall) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : MidOk F 8 slots (after b7 fS) = true ∧
    (after b7 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b7 fS) D6 D7 = true ∧
    (after b7 fS).reg .r13 = some (.bin .add .W64 (.reg .r12) (.bin .shl .W64 (.reg .r13) (.lit 4))) ∧
    (after b7 fS).reg .r14 = some (.lit 1) ∧ (after b7 fS).reg .rbx = some (.lit 0) ∧
    (after b7 fS).reg .r15 = some (.lit 0) := by
  rw [after_eq run_b7]; decide +kernel

public theorem exit_b8 : exec b8 oS = some (after b8 oS,
    .call NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk F 0 slots (after b8 oS) = true ∧
    (after b8 oS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 16] (after b8 oS) DO DOc = true ∧
    (after b8 oS).reg .rdi = some satO ∧ (after b8 oS).reg .rcx = some satO ∧
    (after b8 oS).reg .rsi = some shrO ∧ (after b8 oS).reg .rdx = some aboveO := by
  rw [after_eq run_b8]; decide +kernel

public theorem exit_b9 : exec b9 aS = some (after b9 aS, .cond c9 NativeRustcVmX64.Vm.AccumulateSide.label_7) :=
  run_b9.trans (by rw [after_eq run_b9]; rfl)
public theorem ok_b9 : MidOk F 8 slots (after b9 aS) = true ∧
    (after b9 aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b9 aS) (DOc ++ [(Rg .rax, 35), (Rg .rdx, 36)] ++ DA) DOf = true ∧
    (after b9 aS).reg .r12 = some (.bin .add .W64 (.lit 16) (.reg .r12)) ∧
    (after b9 aS).reg .r14 = some (.bin .xor .W64 (.reg .r14) (.reg .rax)) ∧
    (after b9 aS).reg .r15 = some (.bin .xor .W64 (.reg .r15) (.reg .rdx)) := by
  rw [after_eq run_b9]; decide +kernel

public theorem exit_b10 : exec b10 fS = some (after b10 fS, .jump NativeRustcVmX64.Vm.AccumulateSide.label_8) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem exit_b11 : exec b11 fS = some (after b11 fS, .fall) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem exit_b12 : exec b12 fS = some (after b12 fS, .fall) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b10 : MidOk F 8 slots (after b10 fS) = true ∧
    (after b10 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b10 fS) D12 D12 = true ∧
    MidOk F 8 slots (after b11 fS) = true ∧
    (after b11 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b11 fS) D6 D11 = true ∧
    (after b11 fS).reg .r14 = some (.lit 1) ∧ (after b11 fS).reg .r15 = some (.lit 0) ∧
    MidOk F 8 slots (after b12 fS) = true ∧
    (after b12 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b12 fS) D12 D12 = true ∧
    (after b12 fS).reg .rax = some (.lit 72) := by
  rw [after_eq run_b10, after_eq run_b11, after_eq run_b12]; decide +kernel

end NativeRustcVmX64.Bus.AccumulateSide
