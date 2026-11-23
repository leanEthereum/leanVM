module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingPsi
public meta import NativeRustcVmArm.Code.Vm.RingPsi

/-!
# `ring_psi`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 48-byte frame below SP, region 1 `g` (X2);
- `midS`, after each call (`b1` to `b14`): region 0 `g` (X19);
- `exitS`, at the epilogue (`b15`): region 0 the frame (SP).
-/

namespace NativeRustcVmArm.Ring.Psi

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingPsi

@[expose] public section

/-- At the entry: the frame (region 0) and `g` (region 1, X2). -/
def entryS : SState := init [(48, true), (128, false)] (.ptr 0 48) [(.X2, .ptr 1 0)]

/-- After a call: `g` (region 0, X19). -/
def midS : SState := init [(128, false)] .sp [(.X19, .ptr 0 0)]

/-- At the epilogue: the frame (region 0, SP). -/
def exitS : SState := init [(48, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 midS
sym_block run_b3 := exec b3 midS
sym_block run_b4 := exec b4 midS
sym_block run_b5 := exec b5 midS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 midS
sym_block run_b13 := exec b13 midS
sym_block run_b14 := exec b14 midS
sym_block run_b15 := exec b15 exitS

end NativeRustcVmArm.Ring.Psi
