module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.Powers
public meta import NativeRustcVmArm.Code.Vm.Powers
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `powers`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`: `|out| = 0` returns, `b5`; else the prologue `b1`): region 0 the
  48-byte frame below SP;
- `ldS .X19 0`, at the loop head `.LPowers_2` (`b2`: stores the power in `out[i]` post-indexed,
  calls `EW::mul` for `power·base`): region 0 the slot `out[i]`;
- `regsS`, the loop test (`b3`), the return (`b5`);
- `exitS`, at the epilogue (`b4`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.Powers

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.Powers

@[expose] public section

/-- The prologue: the frame. -/
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
sym_block run_b5e := exec b5 (after b0 entryS)
sym_block run_b2 := exec b2 (ldS .X19 0)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 exitS
sym_block run_b5 := exec b5 regsS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b2_facts : keepsAll (ldS .X19 0) { after b2 (ldS .X19 0) with mem := [] } keptRegs = true ∧
    (∀ w ∈ (after b2 (ldS .X19 0)).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b2 (ldS .X19 0)).mem = some (.reg .X0, i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b2 (ldS .X19 0)).mem = some (.reg .X1, i)) := by
  decide +kernel
public theorem b5e_keeps : keeps entryS (after b5 (after b0 entryS)) = true ∧
    (after b5 (after b0 entryS)).mem = [] := by decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_restores : restores slots 48 (after b4 exitS) = true := by decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) savedRegs = true := by decide +kernel

end NativeRustcVmArm.Arrays.Powers
