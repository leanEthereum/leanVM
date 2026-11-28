module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue
public meta import NativeRustcVmArm.Code.Vm.ComputedBytecodeValue

/-!
# `computed_bytecode_value`'s blocks, run by the symbolic executor

`entryS`, at the entry: region 0 the 32-byte frame below SP; `b0` saves X30, X20, X19, keeps the
value in X20, X19 and calls `multilinear_eval_by`. `retS`, after the call: region 0 the frame (SP);
`b1` compares the result with the value and returns.
-/

namespace NativeRustcVmArm.Bus.ComputedBytecodeValue

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ComputedBytecodeValue

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(32, true)] (.ptr 0 32)

/-- After the call: the frame (region 0) at SP. -/
def retS : SState := init [(32, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS

end NativeRustcVmArm.Bus.ComputedBytecodeValue
