module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingSwitch
public meta import NativeRustcVmArm.Code.Vm.RingSwitch

/-!
# `ring_switch`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 432-byte frame below SP;
- `midS`, between the calls (`b1` to `b4`, `b6`): region 0 the frame (SP);
- `storeS`, at the target's store (`b5`): region 0 the frame, region 1 the `RingW` (X19).
-/

namespace NativeRustcVmArm.Ring.Switch

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingSwitch

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(432, true)] (.ptr 0 432)

/-- Between the calls: the frame (region 0, SP). -/
def midS : SState := init [(432, true)] (.ptr 0 0)

/-- At the target's store: the frame (region 0, SP), the `RingW` (region 1, X19). -/
def storeS : SState := init [(432, true), (16, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 storeS
sym_block run_b6 := exec b6 midS

end NativeRustcVmArm.Ring.Switch
