module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.Dot
public meta import NativeRustcVmArm.Code.Vm.Dot
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `dot`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, then `b1` or `b5`): region 0 the 48-byte frame below SP;
- `ldS r`, at the loop head `.LDot_2` (`b2`, split at its second load: `b2a` loads `left[i]`,
  `b2b` loads `right[i]` and calls `EW::mul`): region 0 the element, `r` its address plus 8;
- `regsS`, after the call (`b3`): no region;
- `exitS`, at the epilogue (`b4`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.Dot

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Dot

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)
/-- At a load: the element, `r` its address plus 8. -/
def ldS (r : XReg) : SState := init [(16, false)] .sp [(r, .ptr 0 8)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At the epilogue: the frame. -/
def exitS : SState := init [(48, true)] (.ptr 0 0)

/-- The loop head's first load. -/
def b2a : List Directive := b2.take 2
/-- The loop head's second load and the call. -/
def b2b : List Directive := b2.drop 2

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X23), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_b2a := exec b2a (ldS .X23)
sym_block run_b2b := exec b2b (ldS .X22)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ r ∈ Arrays.calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b5_frame : ∀ w ∈ (after b5 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48 := by
  decide +kernel

public theorem b5_keeps : keeps entryS (after b5 (after b0 entryS)) = true := by decide +kernel

public theorem b2a_keeps : keepsAll (ldS .X23) (after b2a (ldS .X23))
    (calleeRegs.filter fun r ↦ !inSlots slots r) = true := by
  decide +kernel
public theorem b2b_keeps : keepsAll (ldS .X22) (after b2b (ldS .X22))
    (calleeRegs.filter fun r ↦ !inSlots slots r) = true := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS)
    (calleeRegs.filter fun r ↦ !inSlots slots r) = true := by
  decide +kernel
public theorem b4_restores : restores slots 48 (after b4 exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.Dot
