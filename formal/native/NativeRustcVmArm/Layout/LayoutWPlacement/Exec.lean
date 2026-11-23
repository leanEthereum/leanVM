module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Code.Vm.LayoutWPlacement
public meta import NativeRustcVmArm.Code.Vm.LayoutWPlacement
public meta import NativeRustcVmArm.Layout.Common

/-!
# `LayoutW::placement`'s blocks, run by the symbolic executor

From `entryS`: region 0 the `144` bytes of the layout from `entryAddr = x0 + 24 x1`, the
column's `PlacementAt` at their offset `120`. `b0` loads `present` and branches to `b2` (`0`, returns zeros) or falls
to `b1` (returns the variable count and the index).
-/

namespace NativeRustcVmArm.Layout.LayoutWPlacement

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.LayoutWPlacement NativeRustcVmArm.Layout

@[expose] public section

/-- `x0 + 24 x1`, as `madd` computes it. -/
def entryAddr : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X1) (.lit 24)) (.reg .X0)

/-- At the entry: region 0 from `entryAddr`, the column's `PlacementAt` at its offset `120`. -/
def entryS : SState := init [(144, false)] .sp [] [] [] [(entryAddr, (0, 0))]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b0 entryS)

end NativeRustcVmArm.Layout.LayoutWPlacement
