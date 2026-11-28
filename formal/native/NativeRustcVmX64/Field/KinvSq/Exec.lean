module

public import NativeRustcVmX64.Field.Frame
public meta import NativeRustcVmX64.Field.Frame
public import NativeRustcVmX64.Code.Vm.KinvSq
public meta import NativeRustcVmX64.Code.Vm.KinvSq

/-!
# `kinv::sq`'s blocks, run by the symbolic executor (x86-64)

The prologue `b0` from `frameS 16` (its push and its call's slot), the loop's blocks `b1` (ending
in `call kmul`) and `b2`, and the epilogue `b3` from `midS 16`.
-/

namespace NativeRustcVmX64.Field.KinvSq

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Field NativeRustcVmX64.Vm.KinvSq

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 16)
sym_block run_b1 := exec b1 (midS 16)
sym_block run_b2 := exec b2 (midS 16)
sym_block run_b3 := exec b3 (midS 16)

end NativeRustcVmX64.Field.KinvSq
