module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ColumnWeight
public meta import NativeRustcVmArm.Code.Vm.ColumnWeight
public import NativeRustcVmArm.Whir.Common
public meta import NativeRustcVmArm.Whir.Common

/-!
# `column_weight`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 1104-byte frame below SP (the saved registers at
  the top, the stack point's 66 slots below);
- `retS`, after each call (`b1` then `b2` or `b4`; `b3` then `b4`): region 0 the frame (SP),
  region 1 the `Option<EW>` X19 points to.
-/

namespace NativeRustcVmArm.Ring.Column

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ColumnWeight NativeRustcVmArm.Whir

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(1104, true)] (.ptr 0 1104)

/-- After a call: the frame (region 0, SP), the output (region 1, X19). -/
def retS : SState := init [(1104, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS
sym_block run_b2 := exec b2 (after b1 retS)
sym_block run_b4n := exec b4 (after b1 retS)
sym_block run_b3 := exec b3 retS
sym_block run_b4s := exec b4 (after b3 retS)

end NativeRustcVmArm.Ring.Column
