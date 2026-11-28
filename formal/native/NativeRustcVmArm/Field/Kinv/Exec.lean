module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.Kinv
public meta import NativeRustcVmArm.Code.Vm.Kinv

/-!
# `kinv`'s blocks, run by the symbolic executor

The prologue `b0` (ending in `bl kinv::sq`) from `frameS 32`, the epilogue `b16` (ending in the
tail call `b kinv::sq`) from `epiS 32`, the others (each ending in a call) from `regS`.
-/

namespace NativeRustcVmArm.Field.Kinv

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kinv

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 32)
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 regS
sym_block run_b3 := exec b3 regS
sym_block run_b4 := exec b4 regS
sym_block run_b5 := exec b5 regS
sym_block run_b6 := exec b6 regS
sym_block run_b7 := exec b7 regS
sym_block run_b8 := exec b8 regS
sym_block run_b9 := exec b9 regS
sym_block run_b10 := exec b10 regS
sym_block run_b11 := exec b11 regS
sym_block run_b12 := exec b12 regS
sym_block run_b13 := exec b13 regS
sym_block run_b14 := exec b14 regS
sym_block run_b15 := exec b15 regS
sym_block run_b16 := exec b16 (epiS 32)

end NativeRustcVmArm.Field.Kinv
