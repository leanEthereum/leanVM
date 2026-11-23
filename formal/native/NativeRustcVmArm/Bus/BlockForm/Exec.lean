module

public import NativeRustcVmArm.Code.Vm.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.BlockForm
public meta import NativeRustcVmArm.Code.Vm.BlockForm

/-!
# `block_form`'s blocks, run by the symbolic executor

`b0` (`s0`: region 0 the 64-byte frame, region 1 the `FormBuf` at X5) saves the registers and
sets the form to the constant `side_beta`; `b1` (`s1`: region 0 `TUPLES` at its label, the tuple
below `147`) loads the tuple's span; the loop (`b2` to `b9`, registers only but `b3`, region 0
the weight below X25) adds each slot's scaled form; `b10` (`sF`) returns.
-/

namespace NativeRustcVmArm.Bus.BlockForm

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.BlockForm

@[expose] public section


/-- At the entry: the frame below SP, the form at X5. -/
def s0 : SState := init [(64, true), (5928, false)] (.ptr 0 64) [(.X5, .ptr 1 0)]
/-- `TUPLES` at its label, the tuple below `147`. -/
def s1 : SState := init [(2352, false)] .sp [] [(NativeRustcVmArm.Vm.Symbols.rodata3Label, 0)] [(.reg .X0, 147)]
/-- Registers only. -/
def sR : SState := init [] .sp
/-- The weight below X25. -/
def s3 : SState := init [(16, false)] .sp [(.X25, .ptr 0 8)]
/-- In the frame. -/
def sF : SState := init [(64, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 s0
sym_block run_b1 := exec b1 s1
sym_block run_b2 := exec b2 sR
sym_block run_b3 := exec b3 s3
sym_block run_b4 := exec b4 sR
sym_block run_b5 := exec b5 sR
sym_block run_b6 := exec b6 sR
sym_block run_b7 := exec b7 sR
sym_block run_b8 := exec b8 sR
sym_block run_b9 := exec b9 sR
sym_block run_b10 := exec b10 sF

end NativeRustcVmArm.Bus.BlockForm
