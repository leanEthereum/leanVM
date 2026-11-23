module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcVmArm.Code.Vm.TableTerms.Names
public import NativeRustcVmArm.Tables.TableTerms.Lemmas

/-!
# `table_terms`: what its blocks do

Each block's result as the proofs read it (`ok_b<k>`, checked on the executor's literal results),
the blocks' lengths and places, the labels.
-/

namespace NativeRustcVmArm.Tables.TableTerms

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableTerms
open NativeRustcVmArm.Ring
open NativeRustcVmArm.Bus (after)

@[expose] public section

/-- `TABLES`' label. -/
abbrev tablesL : Label := NativeRustcVmArm.Vm.Symbols.rodata4Label

/-- All callee-saved registers but X30. -/
abbrev cs : List XReg := [.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29]

/-- Registers a block keeps. -/
def keeps (S : SState) (L : List XReg) : Bool := L.all fun r ↦ S.reg r == some (.reg r)

end

public section

theorem keeps_get {S : SState} {L : List XReg} (h : keeps S L = true) {r : XReg} (hr : r ∈ L) :
    S.reg r = some (.reg r) :=
  beq_iff_eq.mp (List.all_eq_true.mp h r hr)

theorem ok_b0 : (after b0 entryS).sp = .ptr 0 0 ∧ slotsOk (after b0 entryS) slots = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 288) ∧
    loadSym (after b0 entryS).mem 0 16 8 = .reg .X0 ∧
    loadSym (after b0 entryS).mem 0 24 8 = .reg .X2 ∧
    loadSym (after b0 entryS).mem 0 32 8 = .reg .X3 ∧
    loadSym (after b0 entryS).mem 0 40 8 = .reg .X4 ∧
    loadSym (after b0 entryS).mem 0 48 8 = .reg .X5 ∧
    loadSym (after b0 entryS).mem 0 56 8 = .reg .X1 ∧
    loadSym (after b0 entryS).mem 0 96 8 = .bin .add .W64 (.load 0 288 8) (.lit 8) ∧
    loadSym (after b0 entryS).mem 0 104 8 = .reg .X6 ∧
    (after b0 entryS).reg .X19 = some (.bin .add .W64 (.label tablesL) (.lit 8)) ∧
    (after b0 entryS).reg .X21 = some (.bin .add .W64 (.label tablesL) (.lit 8)) ∧
    (after b0 entryS).reg .X20 = some (.reg .X7) ∧
    (after b0 entryS).reg .X22 = some (.lit 0) ∧ (after b0 entryS).reg .X23 = some (.lit 0) ∧
    (after b0 entryS).reg .X26 = some (.lit 0) ∧
    (after b0 entryS).reg .X27 = some (.load 0 296 8) ∧
    (after b0 entryS).reg .X29 = some (.lit 240) := by
  rw [Bus.after_eq run_b0]; decide

theorem ok_b1 : (after b1 tabS).sp = .ptr 0 0 ∧ (after b1 tabS).mem = [] ∧
    keeps (after b1 tabS) [.X19, .X20, .X22, .X23, .X26, .X27, .X29] = true ∧
    (after b1 tabS).reg .X21 = some (.bin .add .W64 (.reg .X21) (.lit 40)) ∧
    (after b1 tabS).reg .X28 = some (.load 1 8 8) := by
  rw [Bus.after_eq run_b1]; decide

theorem ok_b2 : (after b2 evS).sp = .ptr 0 0 ∧
    (after b2 evS).mem = [⟨1, 488, 8, .reg .X28⟩] ∧ keeps (after b2 evS) cs = true ∧
    (after b2 evS).reg .X0 = some (.load 0 56 8) ∧
    (after b2 evS).reg .X1 = some (.bin .add .W64 (.reg .X27) (.lit 496)) ∧
    (after b2 evS).reg .X2 = some (.reg .X28) := by
  rw [Bus.after_eq run_b2]; decide

theorem ok_b3 : (after b3 sF).sp = .ptr 0 0 ∧ (after b3 sF).mem = [] ∧
    keeps (after b3 sF) cs = true := by
  rw [Bus.after_eq run_b3]; decide

theorem ok_b4 : (after b4 tab19S).sp = .ptr 0 0 ∧
    wok (after b4 tab19S) [288, 40] [false, false] = true ∧
    fok (after b4 tab19S) [16, 24, 32, 40, 48, 56, 96, 104] = true ∧
    loadSym (after b4 tab19S).mem 0 80 8 = .reg .X23 ∧
    loadSym (after b4 tab19S).mem 0 88 8 = .reg .X22 ∧
    keeps (after b4 tab19S) cs = true ∧
    (after b4 tab19S).reg .X0 = some (.load 1 0 8) ∧
    (after b4 tab19S).reg .X1 = some (.bin .add .W64 (.reg .X27) (.lit 496)) ∧
    (after b4 tab19S).reg .X2 = some (.reg .X28) ∧
    (after b4 tab19S).reg .X3 = some (.ptr 0 112) := by
  rw [Bus.after_eq run_b4]; decide

/-- `b5`'s first argument: the constraint powers from the cursor. -/
abbrev cpS : Sym :=
  .ite (.and (.not (.cmp .ult .W64 (.reg .X26) (.lit 2)))
      (.not (.cmp .eq .W64 (.reg .X26) (.lit 2))))
    (.lit 8) (.bin .add .W64 (.load 0 24 8) (.un (.shift .LSL 4) .W64 (.reg .X26)))

/-- `2 - cursor`, saturated. -/
abbrev restS : Sym :=
  .ite (.cmp .ult .W64 (.lit 2) (.reg .X26)) (.lit 0) (.bin .sub .W64 (.lit 2) (.reg .X26))

theorem ok_b5 : (after b5 tab19S).sp = .ptr 0 0 ∧ (after b5 tab19S).mem = [] ∧
    keeps (after b5 tab19S) [.X19, .X20, .X21, .X24, .X25, .X26, .X27, .X28, .X29] = true ∧
    (after b5 tab19S).reg .X0 = some cpS ∧
    (after b5 tab19S).reg .X1 = some
      (.ite (.cmp .ult .W64 (.load 1 16 8) restS) (.load 1 16 8) restS) ∧
    (after b5 tab19S).reg .X2 = some (.ptr 0 112) ∧
    (after b5 tab19S).reg .X3 = some (.reg .X0) ∧
    (after b5 tab19S).reg .X22 = some (.load 1 16 8) ∧
    (after b5 tab19S).reg .X23 = some (.lit 8) := by
  rw [Bus.after_eq run_b5]; decide

/-- An `evaluate` call's arguments: the form at `o` of region 1. -/
abbrev evalArgs (S : SState) (o : Nat) : Prop :=
  S.sp = .ptr 0 0 ∧ keeps S cs = true ∧
    S.reg .X0 = some (.ite (.cmp .ult .W64 (.load 1 o 8) (.lit 149))
      (.bin .add .W64 (.reg .X20) (.lit (o + 8))) (.reg .X23)) ∧
    S.reg .X1 = some (.ite (.cmp .ult .W64 (.load 1 o 8) (.lit 149)) (.load 1 o 8) (.lit 0)) ∧
    S.reg .X2 = some (.bin .add .W64 (.reg .X27) (.lit 496)) ∧ S.reg .X3 = some (.reg .X28)

theorem ok_b6 : evalArgs (after b6 formS) 0 ∧
    wok (after b6 formS) [288, 17784] [false, false] = true ∧
    fok (after b6 formS) [16, 24, 32, 40, 48, 56, 80, 88, 96, 104] = true ∧
    loadSym (after b6 formS).mem 0 64 8 = .reg .X1 ∧
    loadSym (after b6 formS).mem 0 72 8 = .reg .X0 := by
  rw [Bus.after_eq run_b6]; decide

theorem ok_b7 : evalArgs (after b7 formS) 5928 ∧
    wok (after b7 formS) [288, 17784] [false, false] = true ∧
    fok (after b7 formS) [16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104] = true ∧
    loadSym (after b7 formS).mem 0 144 8 = .reg .X0 ∧
    loadSym (after b7 formS).mem 0 152 8 = .reg .X1 := by
  rw [Bus.after_eq run_b7]; decide

theorem ok_b8 : evalArgs (after b8 formS) 11856 ∧
    wok (after b8 formS) [288, 17784] [false, false] = true ∧
    fok (after b8 formS) [16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 144, 152] = true ∧
    loadSym (after b8 formS).mem 0 160 8 = .reg .X0 ∧
    loadSym (after b8 formS).mem 0 168 8 = .reg .X1 := by
  rw [Bus.after_eq run_b8]; decide

theorem ok_b9 : (after b9 wS).sp = .ptr 0 0 ∧
    wok (after b9 wS) [288, 16] [false, false] = true ∧
    fok (after b9 wS) [16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 144, 152, 160, 168] = true ∧
    loadSym (after b9 wS).mem 0 176 8 = .reg .X0 ∧
    loadSym (after b9 wS).mem 0 184 8 = .reg .X1 ∧
    keeps (after b9 wS) [.X20, .X21, .X22, .X24, .X25, .X26, .X27, .X29] = true ∧
    (after b9 wS).reg .X0 = some (.load 0 32 8) ∧ (after b9 wS).reg .X1 = some (.lit 3) ∧
    (after b9 wS).reg .X2 = some (.ptr 0 144) ∧ (after b9 wS).reg .X3 = some (.lit 3) ∧
    (after b9 wS).reg .X19 = some (.load 0 96 8) ∧
    (after b9 wS).reg .X23 = some (.load 1 8 8) ∧ (after b9 wS).reg .X28 = some (.load 1 0 8) := by
  rw [Bus.after_eq run_b9]; decide

theorem ok_b10 : (after b10 ptS).sp = .ptr 0 0 ∧
    wok (after b10 ptS) [288, 1968, 8] [false, true, false] = true ∧
    fok (after b10 ptS) [16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96] = true ∧
    loadSym (after b10 ptS).mem 0 104 8 = .bin .add .W64 (.load 0 104 8) (.lit 8) ∧
    loadSym (after b10 ptS).mem 1 0 8 = .lit 0 ∧
    keeps (after b10 ptS) [.X19, .X20, .X21, .X22, .X23, .X26, .X27, .X28, .X29] = true ∧
    (after b10 ptS).reg .X0 = some (.reg .X27) ∧
    (after b10 ptS).reg .X1 = some (.load 0 40 8) ∧
    (after b10 ptS).reg .X2 = some (.ite (.cmp .ult .W64 (.load 2 0 8) (.load 0 48 8))
      (.load 2 0 8) (.load 0 48 8)) ∧
    (after b10 ptS).reg .X24 = some (.reg .X0) ∧ (after b10 ptS).reg .X25 = some (.reg .X1) := by
  rw [Bus.after_eq run_b10]; decide

theorem ok_b11 : (after b11 sF).sp = .ptr 0 0 ∧ (after b11 sF).mem = [] ∧
    keeps (after b11 sF) cs = true := by
  rw [Bus.after_eq run_b11]; decide

theorem ok_b12 : (after b12 sF).sp = .ptr 0 0 ∧
    wok (after b12 sF) [288] [false] = true ∧
    fok (after b12 sF) [16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 104] = true ∧
    loadSym (after b12 sF).mem 0 96 8 = .bin .add .W64 (.reg .X19) (.lit 16) ∧
    keeps (after b12 sF) [.X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29] = true ∧
    (after b12 sF).reg .X0 = some (.reg .X28) ∧ (after b12 sF).reg .X1 = some (.reg .X23) ∧
    (after b12 sF).reg .X2 = some (.bin .eor .W64 (.reg .X24) (.load 0 72 8)) ∧
    (after b12 sF).reg .X3 = some (.bin .eor .W64 (.reg .X25) (.load 0 64 8)) := by
  rw [Bus.after_eq run_b12]; decide

theorem ok_b13 : (after b13 sF).sp = .ptr 0 0 ∧ (after b13 sF).mem = [] ∧
    keeps (after b13 sF) [.X21, .X24, .X25, .X28] = true ∧
    (after b13 sF).reg .X19 = some (.reg .X21) ∧
    (after b13 sF).reg .X20 = some (.bin .add .W64 (.reg .X20) (.lit 17784)) ∧
    (after b13 sF).reg .X22 = some (.bin .eor .W64 (.reg .X0) (.load 0 88 8)) ∧
    (after b13 sF).reg .X23 = some (.bin .eor .W64 (.reg .X1) (.load 0 80 8)) ∧
    (after b13 sF).reg .X26 = some (.bin .add .W64 (.reg .X22) (.reg .X26)) ∧
    (after b13 sF).reg .X27 = some (.bin .add .W64 (.reg .X27) (.lit 1968)) ∧
    (after b13 sF).reg .X29 = some (.bin .sub .W64 (.reg .X29) (.lit 40)) := by
  rw [Bus.after_eq run_b13]; decide

theorem ok_b14 : (after b14 outS).sp = .ptr 0 0 ∧
    wok (after b14 outS) [288, 24] [false, true] = true ∧
    keeps (after b14 outS) cs = true ∧
    (∀ w ∈ (after b14 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    loadSym (after b14 outS).mem 1 0 8 = .lit 1 ∧
    loadSym (after b14 outS).mem 1 8 8 = .reg .X22 ∧
    loadSym (after b14 outS).mem 1 16 8 = .reg .X23 := by
  rw [Bus.after_eq run_b14]; decide

theorem ok_b15 : (after b15 outS).sp = .ptr 0 0 ∧
    wok (after b15 outS) [288, 24] [false, true] = true ∧
    keeps (after b15 outS) cs = true ∧
    loadSym (after b15 outS).mem 1 0 8 = .lit 0 := by
  rw [Bus.after_eq run_b15]; decide

theorem ok_b16 : exitOk (after b16 sF) 288 slots [] = true ∧ (after b16 sF).mem = [] := by
  rw [Bus.after_eq run_b16]; decide

/-! ## Places and labels -/


variable [Host] {k : Nat}

theorem addr_eq {a b : Nat} (h : a = b) : Host.addrOf a = Host.addrOf b := by rw [h]

theorem hb0 (hp : Placed code k) : b0.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b0Offset) :=
  b0_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb1 (hp : Placed code k) : b1.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b1Offset) :=
  b1_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb2 (hp : Placed code k) : b2.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b2Offset) :=
  b2_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb3 (hp : Placed code k) : b3.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b3Offset) :=
  b3_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb4 (hp : Placed code k) : b4.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b4Offset) :=
  b4_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb5 (hp : Placed code k) : b5.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b5Offset) :=
  b5_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb6 (hp : Placed code k) : b6.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b6Offset) :=
  b6_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb7 (hp : Placed code k) : b7.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b7Offset) :=
  b7_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb8 (hp : Placed code k) : b8.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b8Offset) :=
  b8_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb9 (hp : Placed code k) : b9.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b9Offset) :=
  b9_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb10 (hp : Placed code k) : b10.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b10Offset) :=
  b10_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb11 (hp : Placed code k) : b11.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b11Offset) :=
  b11_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb12 (hp : Placed code k) : b12.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b12Offset) :=
  b12_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb13 (hp : Placed code k) : b13.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b13Offset) :=
  b13_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb14 (hp : Placed code k) : b14.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b14Offset) :=
  b14_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb15 (hp : Placed code k) : b15.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b15Offset) :=
  b15_in_code.trans hp.1 (List.cons_ne_nil _ _)
theorem hb16 (hp : Placed code k) : b16.IsInfixAt Host.prog (k + NativeRustcVmArm.Vm.TableTerms.b16Offset) :=
  b16_in_code.trans hp.1 (List.cons_ne_nil _ _)

theorem lbl_entry (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.TableTerms.entryLabel = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b0Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.TableTerms.entryOffset) NativeRustcVmArm.Vm.TableTerms.entry_at
theorem lbl_1 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.TableTerms.label_1 = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b1Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.TableTerms.b1Offset) NativeRustcVmArm.Vm.TableTerms.label_1_at
theorem lbl_6 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.TableTerms.label_6 = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b15Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.TableTerms.b15Offset) NativeRustcVmArm.Vm.TableTerms.label_6_at
theorem lbl_7 (hp : Placed code k) : Labels.label NativeRustcVmArm.Vm.TableTerms.label_7 = Host.addrOf (k + NativeRustcVmArm.Vm.TableTerms.b16Offset) :=
  hp.label (j := NativeRustcVmArm.Vm.TableTerms.b16Offset) NativeRustcVmArm.Vm.TableTerms.label_7_at

end

end NativeRustcVmArm.Tables.TableTerms
