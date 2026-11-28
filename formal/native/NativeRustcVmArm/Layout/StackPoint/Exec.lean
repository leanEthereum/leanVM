module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.StackPoint
public meta import NativeRustcVmArm.Code.Vm.StackPoint
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `stack_point`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`: the prologue and the length check): region 0 the 16-byte frame;
- `regsS`, the copy's set-up (`b1`-`b4`, `b6`, `b7`), the call of `selector_point` (`b9`), `b10`;
- `pairS`, a turn of the pair loop `.LStackPoint_5` (`b5`): region 0 the two destination slots,
  region 1 the two source elements;
- `oneS`, a turn of the loop `.LStackPoint_8` (`b8`): region 0 the destination slot, region 1 the
  source element;
- `exitS`, the epilogue (`b11`): region 0 the frame.
-/

namespace NativeRustcVmArm.Layout.StackPoint

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackPoint
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll restores savedRegs)

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(16, true)] (.ptr 0 16)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- A turn of the pair loop: the destination pair (region 0), the source pair (region 1). -/
def pairS : SState := init [(32, false), (32, false)] .sp [(.X12, .ptr 0 16), (.X11, .ptr 1 16)]
/-- A turn of the single loop: the destination slot (region 0), the source (region 1). -/
def oneS : SState := init [(16, false), (16, false)] .sp [(.X11, .ptr 0 8), (.X9, .ptr 1 8)]
/-- At the epilogue: the frame. -/
def exitS : SState := init [(16, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) := [(0, .X30), (8, .X19)]

/-- The registers the body keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b11f := exec b11 (after b0 entryS)
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 pairS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 oneS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 exitS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 16 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false → (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b1_keeps : keepsAll regsS (after b1 regsS) keptRegs = true := by decide +kernel
public theorem b2_keeps : keepsAll regsS (after b2 regsS) keptRegs = true := by decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) keptRegs = true := by decide +kernel
public theorem b7_keeps : keepsAll regsS (after b7 regsS) keptRegs = true := by decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) keptRegs = true := by decide +kernel
public theorem b10_keeps : keepsAll regsS (after b10 regsS) keptRegs = true := by decide +kernel
public theorem b5_facts : keepsAll pairS { after b5 pairS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b5 pairS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ o ∈ [0, 8, 16, 24], ∀ i < 8, findWrite 0 (o + i) (after b5 pairS).mem =
      some (.load 1 o 8, i)) := by
  decide +kernel
public theorem b8_facts : keepsAll oneS { after b8 oneS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b8 oneS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ o ∈ [0, 8], ∀ i < 8, findWrite 0 (o + i) (after b8 oneS).mem = some (.load 1 o 8, i)) := by
  decide +kernel
public theorem b11_restores : restores slots 16 (after b11 exitS) = true ∧
    (after b11 exitS).mem = [] := by decide +kernel

end NativeRustcVmArm.Layout.StackPoint
