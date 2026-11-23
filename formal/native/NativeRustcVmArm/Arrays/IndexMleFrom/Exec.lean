module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.IndexMleFrom
public meta import NativeRustcVmArm.Code.Vm.IndexMleFrom
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `index_mle_from`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, then `b1` or `b7`): region 0 the 64-byte frame below SP;
- `ldS .X20 0`, at the loop head `.LIndexMleFrom_2` (`b2`: loads `r = point[i]` post-indexed,
  calls `EW::mul` for `r·(1 + power)`): region 0 the element;
- `regsS`, after each call (`b3`: `acc·(1 + r·(1 + power))`; `b4`: `power²`; `b5`: the loop test;
  `b6`, `b7`): no region;
- `exitS`, at the epilogue (`b8`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.IndexMleFrom

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.IndexMleFrom

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
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b7 := exec b7 (after b0 entryS)
sym_block run_b2 := exec b2 (ldS .X20 0)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b8 := exec b8 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b7_frame : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b7 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b7 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b7 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b2_facts : keepsAll (ldS .X20 0) (after b2 (ldS .X20 0)) keptRegs = true ∧
    ([XReg.X19, .X21, .X22, .X23, .X24].all fun q ↦ ((ldS .X20 0).reg q).isSome &&
      (after b2 (ldS .X20 0)).reg q == (ldS .X20 0).reg q) = true := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) keptRegs = true := by decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) keptRegs = true := by decide +kernel
public theorem b8_restores : restores slots 64 (after b8 exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.IndexMleFrom
