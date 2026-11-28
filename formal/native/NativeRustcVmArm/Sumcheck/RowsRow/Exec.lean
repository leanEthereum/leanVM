module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RowsRow
public meta import NativeRustcVmArm.Code.Vm.RowsRow

/-!
# `Rows::row`'s block, run by the symbolic executor

`entryS`: region 0 the `Rows` (X0, 32 bytes). `b0` computes the row's slice and returns.
-/

namespace NativeRustcVmArm.Sumcheck.RowsRow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RowsRow

@[expose] public section

/-- At the entry: the `Rows` (region 0, X0). -/
def entryS : SState := init [(32, false)] .sp [(.X0, .ptr 0 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS

end NativeRustcVmArm.Sumcheck.RowsRow
