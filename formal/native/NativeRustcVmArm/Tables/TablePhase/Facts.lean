module

public import NativeRustcVmArm.Tables.TablePhase.Exec
public import NativeRustcVmArm.Tables.PublicInputPhase.Facts

/-!
# `table_phase`: what its blocks do

The frame's slots and kept registers, and each block's result as the proofs read it (`ok_b<k>`,
checked on the executor's literal results).
-/

namespace NativeRustcVmArm.Tables.TablePhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TablePhase
open NativeRustcVmArm.Ring
open NativeRustcVmArm.Tables.PublicInputPhase (WordW)

@[expose] public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(80, .X30), (88, .X23), (96, .X22), (104, .X21), (112, .X20), (120, .X19)]

/-- The callee-saved registers the prologue does not save. -/
abbrev keep : List XReg := [.X24, .X25, .X26, .X27, .X28, .X29]

/-- The registers the blocks between the calls keep. -/
abbrev mids : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

end

public section

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 128 := by decide
theorem slots_hi : ∀ p ∈ slots, 0 + 80 ≤ p.1 ∧ p.1 + 8 ≤ 128 := by decide

theorem ok_b0 : (Bus.after b0 entryS).sp = .ptr 0 0 ∧ slotsOk (Bus.after b0 entryS) slots = true ∧
    (∀ w ∈ (Bus.after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 128) ∧
    (∀ r ∈ keep, (Bus.after b0 entryS).reg r = some (.reg r)) ∧
    (Bus.after b0 entryS).reg .X0 = some (.lit 3) ∧
    (Bus.after b0 entryS).reg .X19 = some (.reg .X3) ∧
    (Bus.after b0 entryS).reg .X20 = some (.reg .X2) ∧
    (Bus.after b0 entryS).reg .X21 = some (.reg .X0) ∧
    (Bus.after b0 entryS).reg .X22 = some (.reg .X1) := by
  rw [Bus.after_eq run_b0]; decide

theorem ok_b1 : (Bus.after b1 sF).sp = .ptr 0 0 ∧ (Bus.after b1 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b1 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b1 sF).reg .X0 = some (.reg .X21) ∧
    (Bus.after b1 sF).reg .X1 = some (.ite (SBool.cmp .ult .W32 (.reg .X0) (.lit 3)) (.lit 0)
      (.bin .sub .W32 (.reg .X0) (.lit 3))) := by
  rw [Bus.after_eq run_b1]; decide

theorem ok_b2 : (Bus.after b2 sF).sp = .ptr 0 0 ∧ (Bus.after b2 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b2 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b2 sF).reg .X0 = some (.lit 0) := by
  rw [Bus.after_eq run_b2]; decide

theorem ok_b3 : (Bus.after b3 sF).sp = .ptr 0 0 ∧ (Bus.after b3 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b3 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b3 sF).reg .X0 = some (.reg .X21) := by
  rw [Bus.after_eq run_b3]; decide

theorem ok_b4 : (Bus.after b4 sF).sp = .ptr 0 0 ∧
    (∀ w ∈ (Bus.after b4 sF).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (∀ r ∈ keep, (Bus.after b4 sF).reg r = some (.reg r)) ∧
    [XReg.X19, .X20, .X21, .X22, .X24, .X25, .X26, .X27, .X28, .X29].all
      (fun r ↦ (Bus.after b4 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b4 sF).reg .X0 = some (.reg .X0) ∧ (Bus.after b4 sF).reg .X1 = some (.reg .X1) ∧
    (Bus.after b4 sF).reg .X2 = some (.ptr 0 0) ∧ (Bus.after b4 sF).reg .X3 = some (.lit 5) ∧
    (Bus.after b4 sF).reg .X23 = some (.ptr 0 0) := by
  rw [Bus.after_eq run_b4]; decide

theorem ok_b5 : (Bus.after b5 sF).sp = .ptr 0 0 ∧ (Bus.after b5 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b5 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b5 sF).reg .X0 = some (.bin .add .W64 (.reg .X23) (.lit 32)) ∧
    (Bus.after b5 sF).reg .X1 = some (.lit 3) ∧
    (Bus.after b5 sF).reg .X2 = some (.bin .add .W64 (.reg .X20) (.lit 107720)) ∧
    (Bus.after b5 sF).reg .X3 = some (.lit 3) := by
  rw [Bus.after_eq run_b5]; decide

theorem ok_b6 : (Bus.after b6 sF).sp = .ptr 0 0 ∧ (Bus.after b6 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b6 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b6 sF).reg .X0 = some (.reg .X21) ∧
    (Bus.after b6 sF).reg .X1 = some (.bin .add .W64 (.reg .X22) (.lit 24)) ∧
    (Bus.after b6 sF).reg .X2 = some (.reg .X20) ∧ (Bus.after b6 sF).reg .X3 = some (.ptr 0 0) ∧
    (Bus.after b6 sF).reg .X4 = some (.bin .add .W64 (.reg .X23) (.lit 32)) ∧
    (Bus.after b6 sF).reg .X5 = some (.reg .X0) ∧ (Bus.after b6 sF).reg .X6 = some (.reg .X1) ∧
    (Bus.after b6 sF).reg .X7 = some (.reg .X19) := by
  rw [Bus.after_eq run_b6]; decide

theorem ok_b7 : exitOk (Bus.after b7 sF) 128 slots keep = true ∧ (Bus.after b7 sF).mem = [] ∧
    (Bus.after b7 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b7]; decide

end

end NativeRustcVmArm.Tables.TablePhase
