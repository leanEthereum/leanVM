module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.GkrLayers
public meta import NativeRustcVmArm.Code.Vm.GkrLayers

/-!
# `gkr_layers`'s blocks, run by the symbolic executor

`entryS`, at the entry: region 0 the 48-byte frame below SP; `b0` saves X30, X22 to X19 and
dispatches on `depth`. `headS`, in the frame (SP its base): every other block.
-/

namespace NativeRustcVmArm.Bus.GkrLayers

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.GkrLayers

@[expose] public section

/-- At the entry: the frame (region 0) below SP. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)

/-- In the frame: region 0 at SP. -/
def headS : SState := init [(48, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 headS
sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 headS
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 headS
sym_block run_b8 := exec b8 headS
sym_block run_b9 := exec b9 headS
sym_block run_b10 := exec b10 headS
sym_block run_b11 := exec b11 headS
sym_block run_b12 := exec b12 headS
sym_block run_b13 := exec b13 headS
sym_block run_b14 := exec b14 headS

end NativeRustcVmArm.Bus.GkrLayers
