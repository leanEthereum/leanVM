module

public import NativeRustcVmArm.Tables.ColumnClaims.Loop

/-!
# `table_column_claims`: the tables' setup blocks and the exits

Each table's setup (`b0` from the entry, `b5`, `b10`, `b15`, `b20`, `b26` in the frame with the
evaluations at X20) reads its point's length and its values' count from its entry, and sets the
loop's registers (`Shapes`): the first value's address, `16 ×` the count (both only below `93`),
the point's address and length (only below `31`), the column before the first. `SB` collects a
setup block with what the executor says of it (`sb1` to `sb5`; `ok_b0` for the prologue). The exits:
the failure (`b24`: X0 zero), the epilogues (`b25`, `b31`: X0 one).
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring
open NativeRustcVmArm.Vm.TableColumnClaims

set_option Elab.async false

@[expose] public section

/-- The loop registers a table's setup sets: table `t`'s entry at offset `1968 t` of region 1, the
column before its first `c`. -/
abbrev Shapes (R : Regs) (t c : Nat) (S : SState) : Prop :=
  S.reg R.a = some (.ite (.cmp .ult .W64 (.load 1 (1968 * t + 488) 8) (.lit 93))
    (.ptr 1 ((1968 * t + 496 : Nat) : Int)) (.lit 8)) ∧
  S.reg R.n = some (.un (.ubfm 60 59) .W64 (.ite (.cmp .ult .W64 (.load 1 (1968 * t + 488) 8)
    (.lit 93)) (.load 1 (1968 * t + 488) 8) (.lit 0))) ∧
  S.reg R.p = some (.ite (.cmp .ult .W64 (.load 1 (1968 * t) 8) (.lit 31))
    (.ptr 1 ((1968 * t + 8 : Nat) : Int)) (.lit 8)) ∧
  S.reg R.l = some (.ite (.cmp .ult .W64 (.load 1 (1968 * t) 8) (.lit 31))
    (.load 1 (1968 * t) 8) (.lit 0)) ∧
  S.reg R.c = some (.lit c)

/-- **A table's setup block** at its place, with what the executor says of it. -/
structure SB [Host] (k : Nat) (R : Regs) (t : Nat) where
  D : List Directive
  j : Nat
  c : Nat
  hc : c + 1 = NativeVm.Model.globalColumnBasesW.getD t 0
  inD : D.IsInfixAt Host.prog (k + j)
  run : exec D setS = some (Bus.after D setS, .fall)
  ok : (Bus.after D setS).mem = [] ∧ (Bus.after D setS).sp = .ptr 0 0 ∧
    [XReg.X19, .X26, .X27, .X28, .X29].all
      (fun r ↦ (Bus.after D setS).reg r == some (.reg r)) = true ∧
    Shapes R t c (Bus.after D setS)
  x20 : t < 5 → (Bus.after D setS).reg .X20 = some (.ptr 1 0)

/-- A block without writes keeping SP and the kept registers. -/
abbrev JumpOk (S : SState) : Prop :=
  S.mem = [] ∧ S.sp = .ptr 0 0 ∧ keep.all (fun r ↦ S.reg r == some (.reg r)) = true

end

public section

theorem ok_b0 : (Bus.after b0 entryS).sp = .ptr 0 0 ∧ slotsOk (Bus.after b0 entryS) slots = true ∧
    (∀ w ∈ (Bus.after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ r ∈ keep, (Bus.after b0 entryS).reg r = some (.reg r)) ∧
    (Bus.after b0 entryS).reg .X19 = some (.reg .X1) ∧
    (Bus.after b0 entryS).reg .X20 = some (.ptr 1 0) ∧ Shapes R04 0 4 (Bus.after b0 entryS) := by
  rw [Bus.after_eq run_b0]; decide

theorem ok_b24 : (Bus.after b24 sF).mem = [] ∧ (Bus.after b24 sF).sp = .ptr 0 0 ∧
    keep.all (fun r ↦ (Bus.after b24 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b24 sF).reg .X0 = some (.lit 0) := by
  rw [Bus.after_eq run_b24]; decide

theorem ok_b25 : exitOk (Bus.after b25 sF) 64 slots keep = true ∧ (Bus.after b25 sF).mem = [] ∧
    (Bus.after b25 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b25]; decide

theorem ok_b31 : exitOk (Bus.after b31 sF) 64 slots keep = true ∧ (Bus.after b31 sF).mem = [] ∧
    (Bus.after b31 sF).reg .X0 = some (.lit 1) := by
  rw [Bus.after_eq run_b31]; decide

theorem ok_b4 : JumpOk (Bus.after b4 sF) := by rw [Bus.after_eq run_b4]; decide
theorem ok_b9 : JumpOk (Bus.after b9 sF) := by rw [Bus.after_eq run_b9]; decide
theorem ok_b14 : JumpOk (Bus.after b14 sF) := by rw [Bus.after_eq run_b14]; decide
theorem ok_b19 : JumpOk (Bus.after b19 sF) := by rw [Bus.after_eq run_b19]; decide
theorem ok_b30 : (Bus.after b30 sF).mem = [] ∧ (Bus.after b30 sF).sp = .ptr 0 0 ∧
    keep.all (fun r ↦ (Bus.after b30 sF).reg r == some (.reg r)) = true ∧
    (Bus.after b30 sF).reg .X0 = some (.reg .X0) := by
  rw [Bus.after_eq run_b30]; decide

end

@[expose] public section

variable [Host] {k : Nat}

/-- Table `1`'s setup. -/
def sb1 (hp : Placed code k) : SB k R04 1 where
  D := b5
  j := 34
  c := 17
  hc := by rw [NativeRustcVm.Tables.bases_eq]; rfl
  inD := b5_in_code.trans hp.1 (by simp [b5])
  run := by rw [Bus.after_eq run_b5]; exact run_b5
  ok := by rw [Bus.after_eq run_b5]; decide
  x20 _ := by rw [Bus.after_eq run_b5]; decide

/-- Table `2`'s setup. -/
def sb2 (hp : Placed code k) : SB k R04 2 where
  D := b10
  j := 62
  c := 30
  hc := by rw [NativeRustcVm.Tables.bases_eq]; rfl
  inD := b10_in_code.trans hp.1 (by simp [b10])
  run := by rw [Bus.after_eq run_b10]; exact run_b10
  ok := by rw [Bus.after_eq run_b10]; decide
  x20 _ := by rw [Bus.after_eq run_b10]; decide

/-- Table `3`'s setup. -/
def sb3 (hp : Placed code k) : SB k R04 3 where
  D := b15
  j := 91
  c := 37
  hc := by rw [NativeRustcVm.Tables.bases_eq]; rfl
  inD := b15_in_code.trans hp.1 (by simp [b15])
  run := by rw [Bus.after_eq run_b15]; exact run_b15
  ok := by rw [Bus.after_eq run_b15]; decide
  x20 _ := by rw [Bus.after_eq run_b15]; decide

/-- Table `4`'s setup. -/
def sb4 (hp : Placed code k) : SB k R04 4 where
  D := b20
  j := 121
  c := 51
  hc := by rw [NativeRustcVm.Tables.bases_eq]; rfl
  inD := b20_in_code.trans hp.1 (by simp [b20])
  run := by rw [Bus.after_eq run_b20]; exact run_b20
  ok := by rw [Bus.after_eq run_b20]; decide
  x20 _ := by rw [Bus.after_eq run_b20]; decide

/-- Table `5`'s setup. -/
def sb5 (hp : Placed code k) : SB k R5 5 where
  D := b26
  j := 158
  c := 65
  hc := by rw [NativeRustcVm.Tables.bases_eq]; rfl
  inD := b26_in_code.trans hp.1 (by simp [b26])
  run := by rw [Bus.after_eq run_b26]; exact run_b26
  ok := by rw [Bus.after_eq run_b26]; decide
  x20 h := absurd h (by decide)

end

end NativeRustcVmArm.Tables.ColumnClaims
