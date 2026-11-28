module

public import NativeRustcArm.Sym

/-!
# Small checks of the symbolic executor

The soundness theorem's axioms; loads that a store covers exactly, partly, or not at all; a
32-bit `mov`, `cmp`/`b.hi`, `csel`, `ror`, `lsr`, `movz`/`movk`.
-/

namespace NativeRustcArm.Sym.Test.Small

set_option Elab.async false

/-- info: 'NativeRustcArm.Sym.exec_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exec_sound

/-- info: 'NativeRustcArm.Sym.match_init' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms match_init

/-- Two byte stores read back as a halfword, an 8-byte store read as its third byte, an unwritten
word, a 32-bit `mov` of it, `cmp` and `b.hi`. -/
def mem : List Directive := [
  .label "L",
  .instr ⟨.W32, .STRB .W1 ⟨.X0, .imm ⟨.int64 0, none⟩⟩⟩,
  .instr ⟨.W32, .STRB .W2 ⟨.X0, .imm ⟨.int64 1, none⟩⟩⟩,
  .instr ⟨.W32, .LDRH .W3 ⟨.X0, .imm ⟨.int64 0, none⟩⟩⟩,
  .instr ⟨.W64, .STR .X4 ⟨.X0, .imm ⟨.int64 8, none⟩⟩⟩,
  .instr ⟨.W32, .LDRB .W5 ⟨.X0, .imm ⟨.int64 10, none⟩⟩⟩,
  .instr ⟨.W32, .LDR .W6 (.addr ⟨.X0, .imm ⟨.int64 16, none⟩⟩)⟩,
  .instr ⟨.W32, .ORR_s .W7 .WZR ⟨.W6, 0, .LSL⟩⟩,
  .instr ⟨.W64, .LDR .X8 (.addr ⟨.X0, .imm ⟨.int64 4, none⟩⟩)⟩,
  .instr ⟨.W64, .SUBS_e .XZR (.X1 : RegOrSp .W64) (.imm ⟨.int64 5, .S0⟩)⟩,
  .instr ⟨.W64, .CSEL .X9 .X1 .X2 .HI⟩,
  .instr ⟨.W64, .EXTR .X10 .X1 .X1 13⟩,
  .instr ⟨.W64, .UBFM .X11 .X1 4 63⟩,
  .instr ⟨.W64, .MOVZ .X12 (.int64 0x1234) .LSL0⟩,
  .instr ⟨.W64, .MOVK .X12 (.int64 0xabcd) .LSL16⟩,
  .instr ⟨.W64, .B_cond .HI (.label "L2")⟩]

/-- X0 points to the 24-byte region 0. -/
def start : SState := init [(24, false)] .sp [(.X0, .ptr 0 0)]

sym_block mem_exec := exec mem start

/-- The halfword stored as two bytes, read back. -/
example : (exec mem start).map (·.1.reg .X3) = some (some (.bin .add .W64
    (.un (.bytes 0 1) .W64 (.reg .X1)) (.un (.shift .LSL 8) .W64 (.un (.bytes 0 1) .W64 (.reg .X2))))) := by
  rw [mem_exec]
  rfl

/-- The third byte of the stored doubleword, and the unwritten word. -/
example : (exec mem start).map (fun r => (r.1.reg .X5, r.1.reg .X6, r.1.reg .X7)) =
    some (some (.un (.bytes 2 1) .W64 (.reg .X4)), some (.load 0 16 4), some (.load 0 16 4)) := by
  rw [mem_exec]
  rfl

/-- The constant `movz`/`movk` build. -/
example : (exec mem start).map (·.1.reg .X12) = some (some (.lit 0xabcd1234)) := by
  rw [mem_exec]
  rfl

end NativeRustcArm.Sym.Test.Small
