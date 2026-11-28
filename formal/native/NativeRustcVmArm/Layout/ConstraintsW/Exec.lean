module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.ConstraintsW
public meta import NativeRustcVmArm.Code.Vm.ConstraintsW
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `constraints_w`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`: not `JUMP` returns `0`, `b5`; else the prologue `b1`): region 0
  the 48-byte frame below SP;
- `rowS n`, the row's loads (`b2` `row[5]`, `b3` `row[12]`, `b4` `row[13]`): region 0 the row's
  first `n` bytes;
- `regsS`, the zeros of a short row (`b6`, `b7`, `b8`) and the first product's call (`b9`);
- `outS`, `out[0]` stored and the second product's call (`b10`): region 0 `out`;
- `exitS`, `out[1]` stored and the epilogue (`b11`): region 0 the frame, region 1 `out`.
-/

namespace NativeRustcVmArm.Layout.ConstraintsW

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ConstraintsW
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll restores savedRegs)

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(48, true)] (.ptr 0 48)
/-- At a load of the row: its first `n` bytes. -/
def rowS (n : Nat) : SState := init [(n, false)] .sp [(.X1, .ptr 0 0)]
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- `out[0]` stored: `out`. -/
def outS : SState := init [(32, false)] .sp [(.X19, .ptr 0 0)]
/-- At the epilogue: the frame and `out`. -/
def exitS : SState := init [(48, true), (32, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(0, .X30), (8, .X23), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

/-- The registers the body keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_b2 := exec b2 (rowS 96)
sym_block run_b3 := exec b3 (rowS 208)
sym_block run_b4 := exec b4 (rowS 224)
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 outS
sym_block run_b11 := exec b11 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b5_keeps : keeps entryS (after b5 (after b0 entryS)) = true ∧
    (after b5 (after b0 entryS)).mem = [] := by decide +kernel
public theorem b2_keeps : keepsAll (rowS 96) (after b2 (rowS 96)) keptRegs = true := by
  decide +kernel
public theorem b3_keeps : keepsAll (rowS 208) (after b3 (rowS 208)) keptRegs = true := by
  decide +kernel
public theorem b4_keeps : keepsAll (rowS 224) (after b4 (rowS 224)) keptRegs = true := by
  decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) keptRegs = true := by decide +kernel
public theorem b7_keeps : keepsAll regsS (after b7 regsS) keptRegs = true := by decide +kernel
public theorem b8_keeps : keepsAll regsS (after b8 regsS) keptRegs = true := by decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) keptRegs = true := by decide +kernel
public theorem b10_facts : keepsAll outS { after b10 outS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b10 outS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b10 outS).mem =
      some (.bin .eor .W64 (.reg .X0) (.reg .X23), i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b10 outS).mem =
      some (.bin .eor .W64 (.reg .X1) (.reg .X22), i)) := by
  decide +kernel
public theorem b11_facts : restores slots 48 (after b11 exitS) = true ∧
    (∀ w ∈ (after b11 exitS).mem, w.r = 1 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b11 exitS).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 1 (24 + i) (after b11 exitS).mem = some (.reg .X1, i)) ∧
    firstOverlap 1 0 16 (after b11 exitS).mem = none := by
  decide +kernel

end NativeRustcVmArm.Layout.ConstraintsW
