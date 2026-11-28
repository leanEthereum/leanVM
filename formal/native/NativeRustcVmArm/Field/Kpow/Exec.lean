module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.Kpow
public meta import NativeRustcVmArm.Code.Vm.Kpow

/-!
# `kpow`'s blocks, run by the symbolic executor

The prologue `b0` from `frameS 32`, the epilogue `b8` from `epiS 32`, the others from `regS`.
-/

namespace NativeRustcVmArm.Field.Kpow

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.Kpow

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 32)
sym_block run_b1 := exec b1 regS
sym_block run_b2 := exec b2 regS
sym_block run_b3 := exec b3 regS
sym_block run_b4 := exec b4 regS
sym_block run_b5 := exec b5 regS
sym_block run_b6 := exec b6 regS
sym_block run_b7 := exec b7 regS
sym_block run_b8 := exec b8 (epiS 32)

end NativeRustcVmArm.Field.Kpow
