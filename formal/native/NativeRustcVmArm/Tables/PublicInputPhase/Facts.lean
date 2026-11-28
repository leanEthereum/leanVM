module

public import NativeRustcVmArm.Tables.PublicInputPhase.Exec
public import NativeRustcVmArm.Tables.Frame

/-!
# `public_input_phase`: what its blocks do

The frame's slots and kept registers, the outputs (the `TState`, the claims), and each block's
result as the proofs read it (`ok_b<k>`, checked on the executor's literal results).
-/

namespace NativeRustcVmArm.Tables.PublicInputPhase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PublicInputPhase
open NativeRustcVmArm.Ring NativeRustcVm.Transcript NativeVm.Model
open NativeRustcVm.Layout (claimsBytes)

@[expose] public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(544, .X29), (560, .X30), (568, .X23), (576, .X22), (584, .X21), (592, .X20), (600, .X19)]

/-- The callee-saved registers the prologue does not save. -/
abbrev keep : List XReg := [.X24, .X25, .X26, .X27, .X28]

/-- The outputs: the `TState` (X0) and the claims (X3). -/
def outs (m0 : MachineData) (q : BitVec 64) : Prop :=
  InRange m0.regs.X0.toBitVec tstateBytes q ∨ InRange m0.regs.X3.toBitVec claimsBytes q

/-- A block's writes: in the frame, its slots apart. -/
def FrameW (S : SState) : Prop :=
  ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 608 ∧ ∀ p ∈ slots, w.off + w.n ≤ p.1 ∨ p.1 + 8 ≤ w.off

instance (S : SState) : Decidable (FrameW S) := by unfold FrameW; infer_instance

/-- The word `v` at offset `o` of the frame. -/
def WordW (S : SState) (o : Nat) (v : Sym) : Prop := ∀ i < 8, findWrite 0 (o + i) S.mem = some (v, i)

instance (S : SState) (o : Nat) (v : Sym) : Decidable (WordW S o v) := by
  unfold WordW; infer_instance

/-- No write at offset `o` of the frame. -/
def NoW (S : SState) (o : Nat) : Prop := ∀ i < 8, findWrite 0 (o + i) S.mem = none

instance (S : SState) (o : Nat) : Decidable (NoW S o) := by unfold NoW; infer_instance

end

public section

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 608 := by decide
theorem N_eq : publicInputPhaseStack = 2432 := by decide

theorem ok_b0 : (Bus.after b0 entryS).sp = .ptr 0 0 ∧ slotsOk (Bus.after b0 entryS) slots = true ∧
    (∀ w ∈ (Bus.after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 608) ∧
    (∀ r ∈ keep, (Bus.after b0 entryS).reg r = some (.reg r)) ∧
    (Bus.after b0 entryS).reg .X0 = some (.reg .X0) ∧
    (Bus.after b0 entryS).reg .X19 = some (.reg .X3) ∧
    (Bus.after b0 entryS).reg .X20 = some (.reg .X2) ∧
    (Bus.after b0 entryS).reg .X23 = some (.reg .X1) := by
  rw [Bus.after_eq run_b0]; decide

theorem ok_b1 : (Bus.after b1 sF).sp = .ptr 0 0 ∧ FrameW (Bus.after b1 sF) ∧
    (∀ r ∈ keep, (Bus.after b1 sF).reg r = some (.reg r)) ∧
    (∀ j < 62, WordW (Bus.after b1 sF) (8 * j) (.lit 0)) ∧
    (Bus.after b1 sF).reg .X0 = some (.reg .X23) ∧ (Bus.after b1 sF).reg .X1 = some (.lit 0) ∧
    (Bus.after b1 sF).reg .X19 = some (.reg .X19) ∧ (Bus.after b1 sF).reg .X20 = some (.reg .X20) ∧
    (Bus.after b1 sF).reg .X21 = some (.reg .X0) ∧ (Bus.after b1 sF).reg .X22 = some (.reg .X1) ∧
    (Bus.after b1 sF).reg .X23 = some (.reg .X23) := by
  rw [Bus.after_eq run_b1]; decide

theorem ok_b2 : (Bus.after b2 sF).sp = .ptr 0 0 ∧ (Bus.after b2 sF).mem = [] ∧
    (∀ r ∈ keep, (Bus.after b2 sF).reg r = some (.reg r)) ∧
    (Bus.after b2 sF).reg .X19 = some (.reg .X19) ∧ (Bus.after b2 sF).reg .X20 = some (.reg .X20) ∧
    (Bus.after b2 sF).reg .X21 = some (.reg .X21) ∧ (Bus.after b2 sF).reg .X22 = some (.reg .X22) ∧
    (Bus.after b2 sF).reg .X23 = some (.ite
      ((SBool.cmp .ult .W64 (.reg .X0) (.lit 1)).not.and (SBool.cmp .eq .W64 (.reg .X0) (.lit 1)).not)
      (.reg .X0) (.lit 1)) := by
  rw [Bus.after_eq run_b2]; decide

theorem ok_b3 : (Bus.after b3 pubS).sp = .ptr 0 0 ∧ FrameW (Bus.after b3 pubS) ∧
    (∀ r ∈ keep, (Bus.after b3 pubS).reg r = some (.reg r)) ∧
    WordW (Bus.after b3 pubS) 0 (.reg .X21) ∧ WordW (Bus.after b3 pubS) 8 (.reg .X22) ∧
    (∀ j < 60, NoW (Bus.after b3 pubS) (16 + 8 * j)) ∧
    WordW (Bus.after b3 pubS) 496 (.load 1 0 8) ∧ WordW (Bus.after b3 pubS) 504 (.lit 0) ∧
    WordW (Bus.after b3 pubS) 512 (.load 1 16 8) ∧ WordW (Bus.after b3 pubS) 520 (.lit 0) ∧
    WordW (Bus.after b3 pubS) 528 (.reg .X21) ∧ WordW (Bus.after b3 pubS) 536 (.reg .X22) ∧
    (Bus.after b3 pubS).reg .X0 = some (.lit 2) ∧ (Bus.after b3 pubS).reg .X1 = some (.ptr 0 496) ∧
    (Bus.after b3 pubS).reg .X2 = some (.lit 2) ∧ (Bus.after b3 pubS).reg .X3 = some (.ptr 0 528) ∧
    (Bus.after b3 pubS).reg .X4 = some (.lit 1) ∧
    (Bus.after b3 pubS).reg .X19 = some (.reg .X19) ∧ (Bus.after b3 pubS).reg .X20 = some (.ptr 1 0) ∧
    (Bus.after b3 pubS).reg .X21 = some (.reg .X21) ∧ (Bus.after b3 pubS).reg .X22 = some (.reg .X22) ∧
    (Bus.after b3 pubS).reg .X23 = some (.reg .X23) := by
  rw [Bus.after_eq run_b3]; decide

theorem ok_b6 : (Bus.after b6 pubS).sp = .ptr 0 0 ∧ FrameW (Bus.after b6 pubS) ∧
    (∀ r ∈ keep, (Bus.after b6 pubS).reg r = some (.reg r)) ∧
    (∀ j < 62, NoW (Bus.after b6 pubS) (8 * j)) ∧
    WordW (Bus.after b6 pubS) 496 (.load 1 8 8) ∧ WordW (Bus.after b6 pubS) 504 (.lit 0) ∧
    WordW (Bus.after b6 pubS) 512 (.load 1 24 8) ∧ WordW (Bus.after b6 pubS) 520 (.lit 0) ∧
    WordW (Bus.after b6 pubS) 528 (.reg .X21) ∧ WordW (Bus.after b6 pubS) 536 (.reg .X22) ∧
    (Bus.after b6 pubS).reg .X0 = some (.lit 2) ∧ (Bus.after b6 pubS).reg .X1 = some (.ptr 0 496) ∧
    (Bus.after b6 pubS).reg .X2 = some (.lit 2) ∧ (Bus.after b6 pubS).reg .X3 = some (.ptr 0 528) ∧
    (Bus.after b6 pubS).reg .X4 = some (.lit 1) ∧
    (Bus.after b6 pubS).reg .X19 = some (.reg .X19) ∧ (Bus.after b6 pubS).reg .X20 = some (.ptr 1 0) ∧
    (Bus.after b6 pubS).reg .X21 = some (.reg .X21) ∧ (Bus.after b6 pubS).reg .X22 = some (.reg .X22) ∧
    (Bus.after b6 pubS).reg .X23 = some (.reg .X23) := by
  rw [Bus.after_eq run_b6]; decide

theorem ok_b4 : (Bus.after b4 sF).sp = .ptr 0 0 ∧ (Bus.after b4 sF).mem = [] ∧
    (∀ r ∈ keep, (Bus.after b4 sF).reg r = some (.reg r)) ∧
    (Bus.after b4 sF).reg .X0 = some (.reg .X19) ∧ (Bus.after b4 sF).reg .X1 = some (.lit 0) ∧
    (Bus.after b4 sF).reg .X2 = some (.ptr 0 0) ∧ (Bus.after b4 sF).reg .X3 = some (.reg .X23) ∧
    (Bus.after b4 sF).reg .X4 = some (.reg .X0) ∧ (Bus.after b4 sF).reg .X5 = some (.reg .X1) ∧
    (Bus.after b4 sF).reg .X19 = some (.reg .X19) ∧ (Bus.after b4 sF).reg .X20 = some (.reg .X20) ∧
    (Bus.after b4 sF).reg .X21 = some (.reg .X21) ∧ (Bus.after b4 sF).reg .X22 = some (.reg .X22) ∧
    (Bus.after b4 sF).reg .X23 = some (.reg .X23) := by
  rw [Bus.after_eq run_b4]; decide

theorem ok_b7 : (Bus.after b7 sF).sp = .ptr 0 0 ∧ (Bus.after b7 sF).mem = [] ∧
    (∀ r ∈ keep, (Bus.after b7 sF).reg r = some (.reg r)) ∧
    (Bus.after b7 sF).reg .X0 = some (.reg .X19) ∧ (Bus.after b7 sF).reg .X1 = some (.lit 1) ∧
    (Bus.after b7 sF).reg .X2 = some (.ptr 0 0) ∧ (Bus.after b7 sF).reg .X3 = some (.reg .X23) ∧
    (Bus.after b7 sF).reg .X4 = some (.reg .X0) ∧ (Bus.after b7 sF).reg .X5 = some (.reg .X1) ∧
    (Bus.after b7 sF).reg .X19 = some (.reg .X19) ∧ (Bus.after b7 sF).reg .X20 = some (.reg .X20) ∧
    (Bus.after b7 sF).reg .X21 = some (.reg .X21) ∧ (Bus.after b7 sF).reg .X22 = some (.reg .X22) ∧
    (Bus.after b7 sF).reg .X23 = some (.reg .X23) := by
  rw [Bus.after_eq run_b7]; decide

theorem ok_b5 : (Bus.after b5 sF).sp = .ptr 0 0 ∧ (Bus.after b5 sF).mem = [] ∧
    (∀ r ∈ keep, (Bus.after b5 sF).reg r = some (.reg r)) ∧
    (Bus.after b5 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b5]; decide

theorem ok_b8 : exitOk (Bus.after b8 sF) 608 slots keep = true ∧ (Bus.after b8 sF).mem = [] ∧
    (Bus.after b8 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b8]; decide

theorem ok_b9 : exitOk (Bus.after b9 sF) 608 slots keep = true ∧ (Bus.after b9 sF).mem = [] ∧
    (Bus.after b9 sF).reg .X0 = some (.lit 0) := by
  rw [Bus.after_eq run_b9]; decide

end

end NativeRustcVmArm.Tables.PublicInputPhase
