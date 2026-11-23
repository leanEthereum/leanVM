module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove
public meta import NativeRustcVmArm.Code.Vm.EqEvalFnOfEqAbove
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `eq_eval_fn` (`eq_above`'s closure)'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, then `b1` or `b5`): region 0 the 48-byte frame below SP;
- `ldS .X21 8`, at the loop head `.LEqEvalFnOfEqAbove_2` (`b2`: loads `right[k]`, forms
  `1 + bit_e(selector, k) + right[k]`, calls `EW::mul`): region 0 the element;
- `regsS`, after the call (`b3`): no region;
- `exitS`, at the epilogue (`b4`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.EqEvalFn

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.EqEvalFnOfEqAbove

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(48, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(0, .X30), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

/-- The registers the loop keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_b2 := exec b2 (ldS .X21 8)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b5_frame : ∀ w ∈ (after b5 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48 := by
  decide +kernel
public theorem b5_keeps : keeps entryS (after b5 (after b0 entryS)) = true := by decide +kernel

public theorem b2_facts : keepsAll (ldS .X21 8) (after b2 (ldS .X21 8)) keptRegs = true ∧
    ([XReg.X0, .X1, .X19, .X20].all fun q ↦ ((ldS .X21 8).reg q).isSome &&
      (after b2 (ldS .X21 8)).reg q == (ldS .X21 8).reg q) = true := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_restores : restores slots 48 (after b4 exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.EqEvalFn
