module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.Kmul
public meta import NativeRustcVmArm.Code.Vm.Kmul

/-!
# `kmul`'s block, run by the symbolic executor

`kmul` is one straight-line block (`b0`), run from `frameS 112` (its 112-byte frame below SP).
-/

namespace NativeRustcVmArm.Field.Kmul

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kmul

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 112)

end NativeRustcVmArm.Field.Kmul
