module

public import NativeRustcVmX64.Bus.AccumulateSide.Exec
public import NativeRustcVmX64.Bus.AccumulateSide.Vals
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove.Names
public meta import NativeRustcVmX64.Bus.AccumulateSide.Exec

/-!
# `accumulate_side`: the prologue's and the known part's blocks (x86-64)

What the executor's summaries say of `b0` to `b5`, checked by the kernel: their exits, their
frames (`ProOk`, `MidOk`), the locations they keep (`trackOk`) and the values they compute.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.AccumulateSide NativeRustcVmX64.Transcript

@[expose] public section

/-- The framework's count as `b0` bounds it. -/
def r13S : Sym := .ite (.cmp .ult .W64 (.load 2 8 8) (.lit 4)) (.load 2 8 8) (.lit 0)
/-- The framework's address as `b0` computes it. -/
def r12S : Sym := .ite (.not (.cmp .ult .W64 (.load 2 8 8) (.lit 4))) (.lit 8)
  (.bin .add .W64 (.load 1 0 8) (.lit 16))
/-- The known part's count. -/
def minS : Sym := .ite (.not (.cmp .ult .W64 (.load 1 16 8) r13S)) r13S (.load 1 16 8)
/-- `b0`'s exit: no known part. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 minS minS) (.lit 0)

/-- What `b0` computes beyond the locations it keeps. -/
def E0 : List (Sym × Nat) := [(Rg .r12, 18), (Rg .r13, 17), (Rg .rdx, 28), (Lw 24, 28)]

/-- What `b1` keeps. -/
def D1 : List (Sym × Nat) :=
  [(Rg .rax, 11), (Rg .rdi, 13), (Rg .r8, 12), (Rg .r9, 26), (Rg .r12, 18)] ++ FWa ++ [(Lw 56, 17)] ++ Dl

/-- `eq_above`'s arguments in `b2a`. -/
def satK : Sym := .ite (.cmp .ult .W64 (.load 1 64 8) (.load 2 0 8)) (.lit 0)
  (.bin .sub .W64 (.load 1 64 8) (.load 2 0 8))
def shrK : Sym := .ite (.not (.cmp .ult .W64 (.load 2 0 8) (.lit 64))) (.lit 0)
  (.bin .shr .W64 (.load 2 8 8) (.load 2 0 8))
def aboveK : Sym := .ite (.cmp .ult .W64 (.load 1 64 8) (.load 2 0 8)) (.reg .r9)
  (.bin .add .W64 (.reg .rdi) (.bin .shl .W64 (.load 2 0 8) (.lit 4)))

/-- `b4`'s exit: more framework blocks. -/
def c4 : SBool := .not (.cmp .eq .W64 (.load 0 24 8) (.bin .add .W64 (.lit 16) (.reg .rbp)))

/-- What `b5` keeps. -/
def D5 : List (Sym × Nat) :=
  [(Rg .rdi, 13), (Rg .r12, 18), (Rg .rbp, 14), (Rg .r13, 17)] ++ FWc ++ [(Lw 16, 2), (Lw 40, 4)] ++ Dl

end

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.AccumulateSide.label_4) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : ProOk F 8 slots (after b0 entryS) = true ∧
    (after b0 entryS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88, 888] (after b0 entryS) DE D0 = true ∧
    (after b0 entryS).reg .r12 = some r12S ∧ (after b0 entryS).reg .r13 = some r13S ∧
    (after b0 entryS).reg .rdx = some minS ∧
    content [12040, 88, 888] (after b0 entryS) (Lw 24) = some minS := by
  rw [after_eq run_b0]; decide +kernel

public theorem exit_b1 : exec b1 fS = some (after b1 fS, .fall) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk F 8 slots (after b1 fS) = true ∧
    (after b1 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b1 fS) (D0 ++ E0) D1 = true ∧
    content [12040] (after b1 fS) (Lw 24) = some (.bin .shl .W64 (.load 0 24 8) (.lit 4)) ∧
    (after b1 fS).reg .rbp = some (.lit 0) ∧ (after b1 fS).reg .r15 = some (.lit 0) ∧
    (after b1 fS).reg .r13 = some (.lit 0) := by
  rw [after_eq run_b1]; decide +kernel

public theorem exit_b2a : exec b2a kAS = some (after b2a kAS, .fall) :=
  run_b2a.trans (by rw [after_eq run_b2a])
public theorem ok_b2a : MidOk F 8 slots (after b2a kAS) = true ∧
    (after b2a kAS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88, 16] (after b2a kAS) (DK ++ DA) D2 = true ∧
    (after b2a kAS).reg .rdi = some satK ∧ (after b2a kAS).reg .rsi = some shrK ∧
    (after b2a kAS).reg .rdx = some aboveK := by
  rw [after_eq run_b2a]; decide +kernel

public theorem exit_b2b : exec b2b kBS = some (after b2b kBS,
    .call NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.entryLabel) :=
  run_b2b.trans (by rw [after_eq run_b2b])
public theorem ok_b2b : MidOk F 0 slots (after b2b kBS) = true ∧
    (after b2b kBS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 16] (after b2b kBS) (D2 ++ E2)
      ([(Rg .r12, 18)] ++ LK ++ FK ++ E2 ++ [(Rg .rcx, 35)]) = true ∧
    (after b2b kBS).reg .rbx = some (.bin .xor .W64 (.load 1 0 8) (.reg .rax)) ∧
    (after b2b kBS).reg .r14 = some (.bin .xor .W64 (.load 1 8 8) (.reg .r8)) := by
  rw [after_eq run_b2b]; decide +kernel

public theorem exit_b3 : exec b3 fS = some (after b3 fS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk F 0 slots (after b3 fS) = true ∧
    (after b3 fS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040] (after b3 fS) (DKc ++ [(Rg .rax, 40), (Rg .rdx, 41)])
      (DKc ++ [(Rg .rdi, 40), (Rg .rsi, 41), (Rg .rdx, 38), (Rg .rcx, 39)]) = true := by
  rw [after_eq run_b3]; decide +kernel

public theorem exit_b4 : exec b4 aS = some (after b4 aS, .cond c4 NativeRustcVmX64.Vm.AccumulateSide.label_2) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : MidOk F 8 slots (after b4 aS) = true ∧
    (after b4 aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b4 aS) (DKc ++ [(Rg .rax, 42), (Rg .rdx, 43)] ++ DA) DKf = true ∧
    (after b4 aS).reg .rbp = some (.bin .add .W64 (.lit 16) (.reg .rbp)) ∧
    (after b4 aS).reg .r15 = some (.bin .xor .W64 (.reg .r15) (.reg .rax)) ∧
    (after b4 aS).reg .r13 = some (.bin .xor .W64 (.reg .r13) (.reg .rdx)) := by
  rw [after_eq run_b4]; decide +kernel

public theorem exit_b5 : exec b5 aS = some (after b5 aS, .fall) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk F 8 slots (after b5 aS) = true ∧
    (after b5 aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b5 aS) (DK ++ DA) D5 = true ∧
    content [12040, 88] (after b5 aS) (Lw 64) =
      some (.bin .xor .W64 (.load 0 64 8) (.reg .r15)) ∧
    content [12040, 88] (after b5 aS) (Lw 72) =
      some (.bin .xor .W64 (.load 0 72 8) (.reg .r13)) := by
  rw [after_eq run_b5]; decide +kernel

end NativeRustcVmX64.Bus.AccumulateSide
