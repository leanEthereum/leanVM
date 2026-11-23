module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.EWMul
public meta import NativeRustcVmArm.Code.Vm.EWMul

/-!
# `EW::mul`'s block, run by the symbolic executor

`EW::mul` is one straight-line block (`b0`), run from `frameS 592` (its 592-byte frame below SP:
96 bytes of saved registers, 496 of spills).
-/

namespace NativeRustcVmArm.Field.EWMul

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.EWMul

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 592)

end NativeRustcVmArm.Field.EWMul
