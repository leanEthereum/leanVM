module

public import NativeRustcVmX64.Bus.AccumulateSide.FactsO
public import NativeRustcVmX64.Code.Vm.AccumulateSide.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public meta import NativeRustcVmX64.Bus.AccumulateSide.Exec

/-!
# `accumulate_side`: the zeroing, the copy and the table loop's setup (x86-64)

What the executor's summaries say of `b13` to `b16`, checked by the kernel.
-/

namespace NativeRustcVmX64.Bus.AccumulateSide

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.AccumulateSide NativeRustcVmX64.Transcript

@[expose] public section

/-- `b13`'s exit: more to clear. -/
def c13 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 80) (.reg .rax)) (.lit 5992))

/-- The tables' count less one. -/
def tm1 : Sym := .bin .sub .W64 (.load 2 64 8) (.lit 1)
/-- `b15`'s exit: no table block, or more than `51`. -/
def c15 : SBool := .and (.not (.cmp .ult .W64 tm1 (.lit 50))) (.not (.cmp .eq .W64 tm1 (.lit 50)))
/-- `b15`'s RCX: the common count of the table blocks and their placements. -/
def rcx15 : Sym :=
  .ite (.not (.cmp .ult .W64 (.load 0 40 8) (.load 2 64 8))) (.load 2 64 8) (.load 0 40 8)

/-- What `b16` keeps. -/
def D16 : List (Sym × Nat) :=
  [(Rg .rdi, 13), (Rg .rbp, 14), (Rg .r8, 27), (Rg .r9, 26)] ++
    [(Lw 96, 3), (Lw 104, 5), (Lw 80, 0), (Lw 64, 20), (Lw 72, 21)] ++ Dl ++
    [(Rg .r14, 22), (Rg .r15, 23), (Rg .r12, 27), (Rg .rsi, 27), (Rg .rdx, 27)]

end

public theorem exit_b13 : exec b13 zS = some (after b13 zS, .cond c13 NativeRustcVmX64.Vm.AccumulateSide.label_9) :=
  run_b13.trans (by rw [after_eq run_b13]; rfl)
public theorem ok_b13 :
    allRegs.all (fun r ↦ r == .rax || (after b13 zS).reg r == some (.reg r)) = true ∧
    (after b13 zS).reg .rax = some (.bin .add .W64 (.lit 80) (.reg .rax)) ∧
    (after b13 zS).mem.all (fun w ↦ w.r == 0 && decide (56 ≤ w.off) && decide (w.off + w.n ≤ 136))
      = true := by
  rw [after_eq run_b13]; decide +kernel

public theorem exit_b14 : exec b14 copyS = some (after b14 copyS, .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk F 0 slots (after b14 copyS) = true ∧
    (after b14 copyS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 8] (after b14 copyS) D12 D14 = true ∧
    (after b14 copyS).reg .rdi = some (.ptr 0 6064) ∧ (after b14 copyS).reg .rsi = some (.ptr 0 136) ∧
    (after b14 copyS).reg .rdx = some (.lit 5920) := by
  rw [after_eq run_b14]; decide +kernel

public theorem exit_b15 : exec b15 slS = some (after b15 slS, .cond c15 NativeRustcVmX64.Vm.AccumulateSide.label_11) :=
  run_b15.trans (by rw [after_eq run_b15]; rfl)
public theorem ok_b15 : MidOk F 8 slots (after b15 slS) = true ∧
    (after b15 slS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88, 888] (after b15 slS) (D14 ++ DA) D14 = true ∧
    (after b15 slS).reg .rcx = some rcx15 := by
  rw [after_eq run_b15]; decide +kernel

public theorem exit_b16 : exec b16 aS = some (after b16 aS, .fall) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : MidOk F 8 slots (after b16 aS) = true ∧
    (after b16 aS).mem.all (fun w ↦ w.r == 0) = true ∧
    trackOk [12040, 88] (after b16 aS) (D15 ++ DA) D16 = true ∧
    content [12040, 88] (after b16 aS) (Lw 40) = some (.bin .shl .W64 (.reg .rcx) (.lit 4)) ∧
    content [12040, 88] (after b16 aS) (Lw 88) =
      some (.bin .add .W64 (.bin .mul .W64 (.load 0 16 8) (.lit 5928)) (.load 0 88 8)) := by
  rw [after_eq run_b16]; decide +kernel

end NativeRustcVmX64.Bus.AccumulateSide
