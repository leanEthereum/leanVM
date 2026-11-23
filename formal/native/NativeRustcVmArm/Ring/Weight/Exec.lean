module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.RingWeight
public meta import NativeRustcVmArm.Code.Vm.RingWeight
public import NativeRustcVmArm.Arrays.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `ring_weight`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`): region 0 the 688-byte frame below SP (the saved registers at
  the top, the 36 powers from byte `16`, `out` at byte `8`);
- `regsS`, the blocks that touch registers only;
- `sumS`, the sum of the coefficients when `|r| = 0` (`b3`): region 0 the four coefficients
  of a turn (X13 − 32);
- `copyS`, the copy of `r`'s pairs (`b7`): region 0 the pair of `r` (X11 − 16), region 1 the
  pair of powers (X12 − 16);
- `lastS`, the copy of `r`'s last element (`b10`): region 0 the element (X11 − 8), region 1 the
  power (X12 − 8);
- `coefS r`, at a coefficient's turn (`b13`, `b22`): region 0 the coefficient (X20 + `r`);
- `prodS`, the product's factor (`b14`): region 0 `r'`'s element (X26 − 8), region 1 the power
  (X29 − 8);
- `sqS r`, a power squared (`b17`, `b18`, `b23`, `b24`): region 0 the power (`r`);
- `exitS`, the epilogue (`b26`): region 0 the frame (SP), region 1 the `Option<EW>` whose
  address the frame keeps at byte `8`.
-/

namespace NativeRustcVmArm.Ring.Weight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.RingWeight NativeRustcVmArm.Arrays

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(688, true)] (.ptr 0 688)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- A turn of the coefficients' sum: four coefficients (region 0, X13 − 32). -/
def sumS : SState := init [(64, false)] .sp [(.X13, .ptr 0 32)]
/-- A turn of the pairs' copy: `r`'s pair (region 0, X11 − 16), the powers' (region 1, X12 − 16). -/
def copyS : SState := init [(32, false), (32, false)] .sp [(.X11, .ptr 0 16), (.X12, .ptr 1 16)]
/-- The last element's copy: `r`'s (region 0, X11 − 8), the power (region 1, X12 − 8). -/
def lastS : SState := init [(16, false), (16, false)] .sp [(.X11, .ptr 0 8), (.X12, .ptr 1 8)]
/-- A coefficient's turn: the coefficient (region 0, X20 + `r`). -/
def coefS (r : XReg) : SState :=
  init [(16, false)] .sp [] [] [] [(.bin .add .W64 (.reg .X20) (.reg r), 0, 0)]
/-- A factor of the product: `r'`'s element (region 0, X26 − 8), the power (region 1, X29 − 8). -/
def prodS : SState := init [(16, false), (16, false)] .sp [(.X26, .ptr 0 8), (.X29, .ptr 1 8)]
/-- A power squared: the power (region 0, `r`). -/
def sqS (r : XReg) : SState := init [(16, false)] .sp [(r, .ptr 0 0)]
/-- The epilogue: the frame (region 0, SP), the output (region 1, the frame's word `8`). -/
def exitS : SState := init [(688, true), (24, false)] (.ptr 0 0) [] [] [] [(.load 0 8 8, 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 sumS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 copyS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 lastS
sym_block run_b11 := exec b11 regsS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 (coefS .X25)
sym_block run_b14 := exec b14 prodS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 (sqS .X29)
sym_block run_b18 := exec b18 (sqS .X29)
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 regsS
sym_block run_b22 := exec b22 (coefS .X24)
sym_block run_b23 := exec b23 (sqS .X26)
sym_block run_b24 := exec b24 (sqS .X26)
sym_block run_b25 := exec b25 regsS
sym_block run_b26 := exec b26 exitS

end NativeRustcVmArm.Ring.Weight
