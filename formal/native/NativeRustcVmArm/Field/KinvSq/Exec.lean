module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.KinvSq
public meta import NativeRustcVmArm.Code.Vm.KinvSq

/-!
# `kinv::sq`'s blocks, run by the symbolic executor

The prologue `b0` from `frameS 16`, the loop's blocks `b1` (ending in `bl kmul`) and `b2` from
`regS`, the epilogue `b3` from `epiS 16`.
-/

namespace NativeRustcVmArm.Field.KinvSq

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.KinvSq

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 16)
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 regS
sym_block run_b3 := exec b3 (epiS 16)

end NativeRustcVmArm.Field.KinvSq
