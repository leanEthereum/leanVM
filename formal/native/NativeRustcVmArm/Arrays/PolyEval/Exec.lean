module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.PolyEval
public meta import NativeRustcVmArm.Code.Vm.PolyEval
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `poly_eval`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, the prologue, falling into the loop): region 0 the 64-byte frame;
- `ldS .X21 8`, at the loop head `.LPolyEval_1` (`b1`: loads the next coefficient from the end,
  calls `EW::mul` on the accumulator and the point): region 0 the coefficient;
- `regsS`, after the call (`b2`): no region;
- `exitS`, at the epilogue (`b3`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.PolyEval

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PolyEval

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(64, true)] (.ptr 0 64)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(64, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (16, .X24), (24, .X23), (32, .X22), (40, .X21), (48, .X20), (56, .X19)]

/-- The registers the loop keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (ldS .X21 8)
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 exitS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b1_facts : keepsAll (ldS .X21 8) (after b1 (ldS .X21 8)) keptRegs = true ∧
    ([XReg.X0, .X1, .X19, .X20, .X21, .X22].all fun q ↦ ((ldS .X21 8).reg q).isSome &&
      (after b1 (ldS .X21 8)).reg q == (ldS .X21 8).reg q) = true := by
  decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS) keptRegs = true := by decide +kernel
public theorem b3_restores : restores slots 64 (after b3 exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.PolyEval
