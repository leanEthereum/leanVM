module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingCoefficients
public meta import NativeRustcVmArm.Code.Vm.RingCoefficients

/-!
# `ring_coefficients`' blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 176-byte frame below SP, region 1 `g` (X1);
- `midS`, in the loop (`b1` to `b17`): region 0 the frame (SP), region 1 the row of `out` the turn
  writes (X26 − 64), region 2 `f`'s element (X27 − 8);
- `exitS`, at the epilogue (`b18`): region 0 the frame (SP).
-/

namespace NativeRustcVmArm.Ring.Coeff

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingCoefficients

@[expose] public section

/-- At the entry: the frame (region 0) and `g` (region 1, X1). -/
def entryS : SState := init [(176, true), (128, false)] (.ptr 0 176) [(.X1, .ptr 1 0)]

/-- In the loop: the frame (region 0, SP), the row (region 1, X26 − 64), `f_p` (region 2,
X27 − 8). -/
def midS : SState :=
  init [(176, true), (128, false), (16, false)] (.ptr 0 0) [(.X26, .ptr 1 64), (.X27, .ptr 2 8)]

/-- At the epilogue: the frame (region 0, SP). -/
def exitS : SState := init [(176, true)] (.ptr 0 0)

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
sym_block run_b15 := exec b15 midS
sym_block run_b16 := exec b16 midS
sym_block run_b17 := exec b17 midS
sym_block run_b18 := exec b18 exitS

end NativeRustcVmArm.Ring.Coeff
