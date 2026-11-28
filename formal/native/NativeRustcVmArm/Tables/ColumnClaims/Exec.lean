module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.TableColumnClaims
public meta import NativeRustcVmArm.Code.Vm.TableColumnClaims

/-!
# `table_column_claims`'s blocks, run by the symbolic executor

Region 0 the 64-byte frame (the saved registers). `entryS` at the entry, the evaluations at X0
(region 1; `b0`: the prologue, table `0`'s slices); `setS` with the evaluations at X20 (table `t`'s
slices: `b5`, `b10`, `b15`, `b20`, `b26`); `sF` in the frame (the loops' heads, the results, the
exits); `bodyS`, `bodyS5` with the value at X8, X9 (region 1; the loops' bodies, `bl push_claim`).
-/

namespace NativeRustcVmArm.Tables.ColumnClaims

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TableColumnClaims

@[expose] public section

/-- At the entry: the frame (region 0) below SP, the evaluations at X0 (region 1). -/
def entryS : SState := init [(64, true), (11808, false)] (.ptr 0 64) [(.X0, .ptr 1 0)]
/-- In the frame, the evaluations at X20. -/
def setS : SState := init [(64, true), (11808, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]
/-- In the frame. -/
def sF : SState := init [(64, true)] (.ptr 0 0)
/-- In the frame, the value at X8. -/
def bodyS : SState := init [(64, true), (16, false)] (.ptr 0 0) [(.X8, .ptr 1 0)]
/-- In the frame, the value at X9. -/
def bodyS5 : SState := init [(64, true), (16, false)] (.ptr 0 0) [(.X9, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 sF
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 setS
sym_block run_b6 := exec b6 sF
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 sF
sym_block run_b9 := exec b9 sF
sym_block run_b10 := exec b10 setS
sym_block run_b11 := exec b11 sF
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 sF
sym_block run_b14 := exec b14 sF
sym_block run_b15 := exec b15 setS
sym_block run_b16 := exec b16 sF
sym_block run_b17 := exec b17 bodyS
sym_block run_b18 := exec b18 sF
sym_block run_b19 := exec b19 sF
sym_block run_b20 := exec b20 setS
sym_block run_b21 := exec b21 sF
sym_block run_b22 := exec b22 bodyS
sym_block run_b23 := exec b23 sF
sym_block run_b24 := exec b24 sF
sym_block run_b25 := exec b25 sF
sym_block run_b26 := exec b26 setS
sym_block run_b27 := exec b27 sF
sym_block run_b28 := exec b28 bodyS5
sym_block run_b29 := exec b29 sF
sym_block run_b30 := exec b30 sF
sym_block run_b31 := exec b31 sF

end NativeRustcVmArm.Tables.ColumnClaims
