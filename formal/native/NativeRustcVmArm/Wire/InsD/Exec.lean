module

public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.InsD
public meta import NativeRustcVmArm.Code.Vm.InsD

/-!
# `ins_d`'s blocks, run by the symbolic executor

`ins_d` uses no stack; each element access `[x0, xk, lsl #3]` of index `xk & 255` is placed by an
alias (`elem x`) at a region of one element.

- `regS`: no region: the start (`b0`), the check of the scan's step (`b2`), the shift's set-up
  (`b6`).
- `scanS`: region 0 the element at X8: the scan's load and comparison (`b1`), then `b4`, `b5`.
- `endS`: region 0 the element at X1: `x` at the end (`b3`).
- `atS`: region 0 the element at X8: `x` in place (`b8`).
- `shiftS`: region 0 the element at X9 minus one, region 1 the one at X9: a step of the shift (`b7`).
-/

namespace NativeRustcVmArm.Wire.InsD

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InsD

@[expose] public section

/-- The state `exec ds S` ends in (`S` where it fails). -/
def after (ds : List Directive) (S : SState) : SState :=
  match exec ds S with
  | some (S', _) => S'
  | none => S

/-- The address of the element of index `x & 255` (`[x0, xk, lsl #3]`). -/
def elem (x : Sym) : Sym :=
  mkBin .add .W64 (.reg .X0) (mkUn (.memExtend ⟨.UXTX, .E3⟩) .W64 (mkBin .and .W64 x (.lit 255)))

/-- No region. -/
def regS : SState := init [] .sp

/-- The element at X8. -/
def scanS : SState := init [(8, false)] .sp [] [] [] [(elem (.reg .X8), 0, 0)]

/-- The element at X1. -/
def endS : SState := init [(8, false)] .sp [] [] [] [(elem (.reg .X1), 0, 0)]

/-- The elements at X9 minus one and at X9. -/
def shiftS : SState := init [(8, false), (8, false)] .sp [] [] []
  [(elem (mkBin .sub .W64 (.reg .X9) (.lit 1)), 0, 0), (elem (.reg .X9), 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 regS
sym_block run_b1 := exec b1 scanS
sym_block run_b2 := exec b2 (after b1 scanS)
sym_block run_b4 := exec b4 (after b1 scanS)
sym_block run_b5 := exec b5 (after b4 (after b1 scanS))
sym_block run_b3 := exec b3 endS
sym_block run_b6 := exec b6 regS
sym_block run_b7 := exec b7 shiftS
sym_block run_b8 := exec b8 scanS

end NativeRustcVmArm.Wire.InsD
