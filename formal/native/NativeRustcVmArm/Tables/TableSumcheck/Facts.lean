module

public import NativeRustcVmArm.Code.Vm.TableSumcheck.Names
public import NativeRustcVmArm.Tables.TableSumcheck.Exec
public import NativeRustcVmArm.Bus.Common

/-!
# `table_sumcheck`: what its blocks do

The frame's slots (every callee-saved register and X30, at `624` on), and each block's result as
the proofs read it (`ok_b<k>`, checked on the executor's literal results). `maxS`: the heights'
maximum `b0` leaves in X25 (`hmax` of the six words in turn); `hiS`: `b.hi` after a comparison.
-/

namespace NativeRustcVmArm.Tables.TableSumcheck

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableSumcheck
open NativeRustcVmArm.Ring

@[expose] public section

/-- The frame's saved registers. -/
abbrev slots : List (Nat × XReg) :=
  [(624, .X29), (632, .X30), (640, .X28), (648, .X27), (656, .X26), (664, .X25), (672, .X24),
    (680, .X23), (688, .X22), (696, .X21), (704, .X20), (712, .X19)]

/-- The callee-saved registers the prologue does not save: none. -/
abbrev keep : List XReg := []

/-- The registers the blocks between the calls keep. -/
abbrev mids : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

/-- `b.hi` after `cmp x, #v`. -/
def hiS (x : Sym) (v : Nat) : SBool :=
  .and (.not (.cmp .ult .W64 x (.lit v))) (.not (.cmp .eq .W64 x (.lit v)))

/-- `csel x, b, a, hi` after `cmp b, a`: the larger. -/
def hmax (a b : Sym) : Sym :=
  .ite (.and (.not (.cmp .ult .W64 b a)) (.not (.cmp .eq .W64 b a))) b a

/-- The six heights' maximum, as `b0` computes it. -/
def maxS : Sym :=
  hmax (hmax (hmax (hmax (hmax (.load 1 0 8) (.load 1 8 8)) (.load 1 16 8)) (.load 1 24 8))
    (.load 1 32 8)) (.load 1 40 8)

/-- `b9`'s comparison: the final sum's halves against the claim's (X26, X27). -/
def eqS : SBool :=
  .ite (.cmp .eq .W64 (.load 0 608 8) (.reg .X26)) (.cmp .eq .W64 (.load 0 616 8) (.reg .X27))
    (.lit false)

end

public section

theorem keep_callee : ∀ r ∈ keep, calleeSaved r = true := by decide
theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 720 := by decide
theorem slots_hi : ∀ p ∈ slots, 624 ≤ p.1 ∧ p.1 + 8 ≤ 720 := by decide

theorem run_b0' : exec b0 entryS =
    some (Bus.after b0 entryS, .cond (hiS maxS 30) NativeRustcVmArm.Vm.TableSumcheck.label_7) := by
  rw [Bus.after_eq run_b0]; exact run_b0.trans rfl

theorem ok_b0 : (Bus.after b0 entryS).sp = .ptr 0 0 ∧ slotsOk (Bus.after b0 entryS) slots = true ∧
    (∀ w ∈ (Bus.after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 720) ∧
    (Bus.after b0 entryS).reg .X0 = some (.reg .X0) ∧
    (Bus.after b0 entryS).reg .X1 = some (.ptr 1 0) ∧
    (Bus.after b0 entryS).reg .X2 = some (.reg .X2) ∧
    (Bus.after b0 entryS).reg .X3 = some (.reg .X3) ∧
    (Bus.after b0 entryS).reg .X4 = some (.reg .X4) ∧
    (Bus.after b0 entryS).reg .X5 = some (.reg .X5) ∧
    (Bus.after b0 entryS).reg .X6 = some (.reg .X6) ∧
    (Bus.after b0 entryS).reg .X7 = some (.reg .X7) ∧
    (Bus.after b0 entryS).reg .X25 = some maxS := by
  rw [Bus.after_eq run_b0]
  exact ⟨rfl, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ok_b1 : (Bus.after b1 sF).sp = .ptr 0 0 ∧ (Bus.after b1 sF).mem = [] ∧
    (Bus.after b1 sF).reg .X0 = some (.ptr 0 504) ∧ (Bus.after b1 sF).reg .X1 = some (.reg .X0) ∧
    (Bus.after b1 sF).reg .X2 = some (.reg .X5) ∧ (Bus.after b1 sF).reg .X3 = some (.reg .X6) ∧
    (Bus.after b1 sF).reg .X4 = some (.lit 4) ∧ (Bus.after b1 sF).reg .X5 = some (.ptr 0 24) ∧
    (Bus.after b1 sF).reg .X6 = some (.reg .X25) ∧
    (Bus.after b1 sF).reg .X19 = some (.reg .X2) ∧ (Bus.after b1 sF).reg .X20 = some (.reg .X4) ∧
    (Bus.after b1 sF).reg .X21 = some (.reg .X1) ∧ (Bus.after b1 sF).reg .X22 = some (.reg .X3) ∧
    (Bus.after b1 sF).reg .X23 = some (.reg .X0) ∧ (Bus.after b1 sF).reg .X24 = some (.reg .X7) ∧
    (Bus.after b1 sF).reg .X25 = some (.reg .X25) := by
  rw [Bus.after_eq run_b1]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ok_b2 : (Bus.after b2 sF).sp = .ptr 0 0 ∧ (Bus.after b2 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b2 sF).reg r == some (.reg r)) = true := by
  rw [Bus.after_eq run_b2]; decide

theorem run_b2' : exec b2 sF = some (Bus.after b2 sF,
    .cond (.cmp .eq .W64 (.load 0 504 8) (.lit 0)) NativeRustcVmArm.Vm.TableSumcheck.label_7) := by
  rw [Bus.after_eq run_b2]; exact run_b2

theorem ok_b3 : (Bus.after b3 sF).sp = .ptr 0 0 ∧ (Bus.after b3 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b3 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b3 sF).reg .X8 = some (.un (.ubfm 1 63) .W64 (.reg .X25)) := by
  rw [Bus.after_eq run_b3]; decide

theorem run_b3' : exec b3 sF = some (Bus.after b3 sF,
    .cond (.cmp .eq .W64 (.un (.ubfm 1 63) .W64 (.reg .X25)) (.lit 0)) NativeRustcVmArm.Vm.TableSumcheck.label_5) := by
  rw [Bus.after_eq run_b3]; exact run_b3

theorem ok_b4 : (Bus.after b4 sF).sp = .ptr 0 0 ∧ (Bus.after b4 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b4 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b4 sF).reg .X8 = some (.reg .X8) ∧ (Bus.after b4 sF).reg .X9 = some (.ptr 0 24) ∧
    (Bus.after b4 sF).reg .X10 = some (.bin .sub .W64
      (.bin .add .W64 (.ptr 0 24) (.un (.shift .LSL 4) .W64 (.reg .X25))) (.lit 16)) := by
  rw [Bus.after_eq run_b4]; decide

theorem ok_b5 : (Bus.after b5 revS).sp = .sp ∧
    (Bus.after b5 revS).mem = [⟨1, 8, 8, .load 0 8 8⟩, ⟨1, 0, 8, .load 0 0 8⟩,
      ⟨0, 8, 8, .load 1 8 8⟩, ⟨0, 0, 8, .load 1 0 8⟩] ∧
    mids.all (fun r ↦ (Bus.after b5 revS).reg r == some (.reg r)) = true ∧
    (Bus.after b5 revS).reg .X8 = some (.bin .sub .W64 (.reg .X8) (.lit 1)) ∧
    (Bus.after b5 revS).reg .X9 = some (.ptr 0 16) ∧
    (Bus.after b5 revS).reg .X10 = some (.ptr 1 (-16)) := by
  rw [Bus.after_eq run_b5]; decide

theorem run_b5' : exec b5 revS = some (Bus.after b5 revS,
    .cond (.not (.cmp .eq .W64 (.bin .sub .W64 (.reg .X8) (.lit 1)) (.lit 0)))
      NativeRustcVmArm.Vm.TableSumcheck.label_4) := by
  rw [Bus.after_eq run_b5]; exact run_b5

theorem ok_b6 : (Bus.after b6 busS).sp = .ptr 0 0 ∧ (Bus.after b6 busS).mem = [] ∧
    [XReg.X20, .X21, .X22, .X23, .X24, .X25, .X29].all
      (fun r ↦ (Bus.after b6 busS).reg r == some (.reg r)) = true ∧
    (Bus.after b6 busS).reg .X19 = some (.ptr 1 0) ∧
    (Bus.after b6 busS).reg .X0 = some (.ptr 0 504) ∧
    (Bus.after b6 busS).reg .X1 = some (.reg .X21) ∧
    (Bus.after b6 busS).reg .X2 = some (.ite (.cmp .ult .W64 (.load 1 106704 8) (.lit 64))
      (.ptr 1 106712) (.lit 8)) ∧
    (Bus.after b6 busS).reg .X3 = some (.ite (.cmp .ult .W64 (.load 1 106704 8) (.lit 64))
      (.load 1 106704 8) (.lit 0)) ∧
    (Bus.after b6 busS).reg .X4 = some (.ptr 0 24) ∧
    (Bus.after b6 busS).reg .X5 = some (.reg .X25) ∧
    (Bus.after b6 busS).reg .X26 = some (.load 0 512 8) ∧
    (Bus.after b6 busS).reg .X27 = some (.load 0 520 8) ∧
    (Bus.after b6 busS).reg .X28 = some (.ptr 0 504) := by
  rw [Bus.after_eq run_b6]
  exact ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ok_b7 : (Bus.after b7 sF).sp = .ptr 0 0 ∧
    (Bus.after b7 sF).mem = [⟨0, 8, 8, .reg .X24⟩, ⟨0, 0, 8, .reg .X28⟩] ∧
    mids.all (fun r ↦ (Bus.after b7 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b7 sF).reg .X0 = some (.ptr 0 600) ∧ (Bus.after b7 sF).reg .X1 = some (.reg .X23) ∧
    (Bus.after b7 sF).reg .X2 = some (.reg .X22) ∧ (Bus.after b7 sF).reg .X3 = some (.reg .X20) ∧
    (Bus.after b7 sF).reg .X4 = some (.ptr 0 24) ∧ (Bus.after b7 sF).reg .X5 = some (.reg .X25) ∧
    (Bus.after b7 sF).reg .X6 = some (.reg .X21) ∧ (Bus.after b7 sF).reg .X7 = some (.reg .X19) :=
  by
  rw [Bus.after_eq run_b7]
  exact ⟨rfl, rfl, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ok_b8 : (Bus.after b8 sF).sp = .ptr 0 0 ∧ (Bus.after b8 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b8 sF).reg r == some (.reg r)) = true := by
  rw [Bus.after_eq run_b8]; decide

theorem run_b8' : exec b8 sF = some (Bus.after b8 sF,
    .cond (.not (.bit .W32 (.load 0 600 4) 0)) NativeRustcVmArm.Vm.TableSumcheck.label_7) := by
  rw [Bus.after_eq run_b8]; exact run_b8

theorem ok_b9 : (Bus.after b9 sF).sp = .ptr 0 0 ∧ (Bus.after b9 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b9 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b9 sF).reg .X0 = some (.ite (.not eqS) (.lit 0) (.lit 1)) := by
  rw [Bus.after_eq run_b9]
  exact ⟨rfl, rfl, by decide, rfl⟩

theorem ok_b10 : (Bus.after b10 sF).sp = .ptr 0 0 ∧ (Bus.after b10 sF).mem = [] ∧
    mids.all (fun r ↦ (Bus.after b10 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b10 sF).reg .X0 = some (.lit 0) := by
  rw [Bus.after_eq run_b10]; decide

theorem ok_b11 : exitOk (Bus.after b11 sF) 720 slots keep = true ∧ (Bus.after b11 sF).mem = [] ∧
    (Bus.after b11 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b11]; decide

end

end NativeRustcVmArm.Tables.TableSumcheck
