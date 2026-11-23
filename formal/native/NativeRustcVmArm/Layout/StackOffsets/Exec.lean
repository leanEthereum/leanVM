module

public import NativeRustcVmArm.Layout.Common
public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Layout.InsertionSort.Exec
public import NativeRustcVmArm.Code.Vm.StackOffsets
public meta import NativeRustcVmArm.Code.Vm.StackOffsets
public meta import NativeRustcVmArm.Layout.Common
public meta import NativeRustcVmArm.Arrays.Common
public meta import NativeRustcVmArm.Layout.InsertionSort.Exec

/-!
# `stack_offsets`' blocks, run by the symbolic executor

- `entryS`, at the entry: region 0 the 1328-byte frame (`b0`; from there the return `b1` and the
  prologue `b2`, which calls `memset`);
- `regsS`: no memory (`b3`-`b7`, `b9`, `b10`, `b12`-`b17`, `b22`);
- `quadS`, a turn of the 4-at-a-time loop (`b8`): region 0 the four words, X11 its byte `16`;
- `wordS`, a turn of the single-store loop (`b11`) or the main loop's load of `order[k]`
  (`b18`): region 0 the word at X9;
- `ixS p i`: region 0 the word at `[p, i, lsl #3]` (`b19`'s store into `offsets`, `b20`'s load
  of `sizes[i]`);
- `exitS`, the epilogues (`b21`, `b23`): region 0 the frame.
-/

namespace NativeRustcVmArm.Layout.StackOffsets

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.StackOffsets
open NativeRustcVmArm.Arrays (calleeRegs inSlots keepsAll restores savedRegs)
open NativeRustcVmArm.Layout.InsertionSort (idx)

@[expose] public section

/-- At the entry: the frame, SP its top. -/
def entryS : SState := init [(1328, true)] (.ptr 0 1328)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- A turn of the 4-at-a-time loop: the four words (region 0), X11 at byte `16`. -/
def quadS : SState := init [(32, false)] .sp [(.X11, .ptr 0 16)]
/-- A store or load at X9: the word (region 0). -/
def wordS : SState := init [(8, false)] .sp [(.X9, .ptr 0 0)]
/-- An access at `[p, i, lsl #3]`: the word (region 0). -/
def ixS (p i : XReg) : SState := init [(8, false)] .sp [] [] [] [(idx p i, 0, 0)]
/-- At an epilogue: the frame, SP its base. -/
def exitS : SState := init [(1328, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(1264, .X29), (1272, .X30), (1280, .X24), (1288, .X23), (1296, .X22), (1304, .X21),
    (1312, .X20), (1320, .X19)]

/-- The registers the body keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 (after b0 entryS)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 quadS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 wordS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 wordS
sym_block run_b19 := exec b19 (ixS .X20 .X11)
sym_block run_b20 := exec b20 (ixS .X22 .X11)
sym_block run_b21 := exec b21 exitS
sym_block run_b22 := exec b22 regsS
sym_block run_b23 := exec b23 exitS

public theorem b1_ret :
    (savedRegs.all fun r ↦ (after b1 (after b0 entryS)).reg r == some (.reg r)) ∧
    (after b1 (after b0 entryS)).sp = .ptr 0 1328 ∧ (after b1 (after b0 entryS)).mem = [] := by
  decide +kernel

public theorem b2_frame : (after b2 (after b0 entryS)).sp = .ptr 0 0 ∧
    (∀ p ∈ slots, p.1 + 8 ≤ 1328 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b2 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b2 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 1328) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b2 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) keptRegs = true := by decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) keptRegs = true := by decide +kernel
public theorem b7_keeps : keepsAll regsS (after b7 regsS) keptRegs = true := by decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) keptRegs = true := by decide +kernel
public theorem b10_keeps : keepsAll regsS (after b10 regsS) keptRegs = true := by decide +kernel
public theorem b12_keeps : keepsAll regsS (after b12 regsS) keptRegs = true := by decide +kernel
public theorem b13_keeps : keepsAll regsS (after b13 regsS) keptRegs = true := by decide +kernel
public theorem b14_keeps : keepsAll regsS (after b14 regsS) keptRegs = true := by decide +kernel
public theorem b16_keeps : keepsAll regsS (after b16 regsS) keptRegs = true := by decide +kernel
public theorem b17_keeps : keepsAll regsS (after b17 regsS) keptRegs = true := by decide +kernel
public theorem b22_keeps : keepsAll regsS (after b22 regsS) keptRegs = true := by decide +kernel
public theorem b18_keeps : keepsAll wordS (after b18 wordS) keptRegs = true := by decide +kernel
public theorem b20_keeps :
    keepsAll (ixS .X22 .X11) (after b20 (ixS .X22 .X11)) keptRegs = true := by
  decide +kernel

public theorem b8_facts : keepsAll quadS { after b8 quadS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b8 quadS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b8 quadS).mem =
      some (.bin .sub .W64 (.reg .X12) (.lit 1), i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b8 quadS).mem = some (.reg .X12, i)) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b8 quadS).mem =
      some (.bin .add .W64 (.reg .X12) (.lit 1), i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b8 quadS).mem =
      some (.bin .add .W64 (.reg .X12) (.lit 2), i)) := by
  decide +kernel

public theorem b11_facts : keepsAll wordS { after b11 wordS with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b11 wordS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b11 wordS).mem = some (.reg .X8, i)) := by
  decide +kernel

public theorem b19_facts :
    keepsAll (ixS .X20 .X11) { after b19 (ixS .X20 .X11) with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b19 (ixS .X20 .X11)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b19 (ixS .X20 .X11)).mem = some (.reg .X8, i)) := by
  decide +kernel

public theorem b21_restores : restores slots 1328 (after b21 exitS) = true ∧
    (after b21 exitS).mem = [] := by decide +kernel
public theorem b23_restores : restores slots 1328 (after b23 exitS) = true ∧
    (after b23 exitS).mem = [] := by decide +kernel

end NativeRustcVmArm.Layout.StackOffsets
