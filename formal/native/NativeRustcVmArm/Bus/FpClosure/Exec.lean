module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0
public meta import NativeRustcVmArm.Code.Vm.VerifyBusBalanceClosure0

/-!
# `verify_bus_balance::{closure#0}`'s blocks, run by the symbolic executor

`b0` is split after its loads from the environment (`b0a`, region 1 the environment at X1), since
its next load goes through the share's address the environment holds (`b0b`, region 1 the share at
X14). Region 0 is the 64-byte frame.
-/

namespace NativeRustcVmArm.Bus.FpClosure

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyBusBalanceClosure0

@[expose] public section

/-- At the entry: the frame below SP, the environment at X1 (region 1). -/
def s0 : SState := init [(64, true), (56, false)] (.ptr 0 64) [(.X1, .ptr 1 0)]
/-- In the frame, the share at X14 (region 1). -/
def s1 : SState := init [(64, true), (16, false)] (.ptr 0 0) [(.X14, .ptr 1 0)]
/-- In the frame. -/
def sF : SState := init [(64, true)] (.ptr 0 0)

/-- `b0`'s loads from the environment. -/
def b0a : List Directive := b0.take 6
/-- The rest of `b0`: the share's load, the arguments, the call. -/
def b0b : List Directive := b0.drop 6

end

set_option Elab.async false

sym_block run_b0a := exec b0a s0
sym_block run_b0b := exec b0b s1
sym_block run_b1 := exec b1 sF

end NativeRustcVmArm.Bus.FpClosure
