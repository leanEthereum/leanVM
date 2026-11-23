module

public import NativeRustcVmArm.Field.Frame
public meta import NativeRustcVmArm.Field.Frame
public import NativeRustcVmArm.Code.Vm.BitLength
public meta import NativeRustcVmArm.Code.Vm.BitLength

/-!
# `bit_length`'s block, run by the symbolic executor

`bit_length` is one straight-line block (`b0`) without memory accesses, run from `regS`.
-/

namespace NativeRustcVmArm.Field.BitLength

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Field NativeRustcVmArm.Vm.BitLength

set_option Elab.async false

sym_block run_b0 := exec b0 regS

end NativeRustcVmArm.Field.BitLength
