module

public import NativeRustcVmArm.Arrays.Common
public import NativeRustcVmArm.Code.Vm.PaddingWeight
public meta import NativeRustcVmArm.Code.Vm.PaddingWeight
public meta import NativeRustcVmArm.Arrays.Common

/-!
# `padding_weight`'s blocks, run by the symbolic executor

- `entryS`, at the entry (`b0`, then `b1` or `b6`): region 0 the 112-byte frame below SP (the
  callee-saved registers, X29, X30, and `|point|` at offset 8);
- `ldS .X22 0`, at the loop head `.LPaddingWeight_2` (`b2`: `1 + b` from bit `k` of `n`, loads
  `r = point[k]` post-indexed, calls `EW::mul` for `(1 + b)·r`): region 0 the element;
- `regsS`, after the calls (`b3`: `(1 + b + r)·pad`; `b4`: the sum, the loop test; `b5`): no region;
- `exitS`, at `.LPaddingWeight_4` (`b7`: `1 + b` from bit `|point|` of `n`, the epilogue, the tail
  call `(1 + b)·pad`): region 0 the frame.
-/

namespace NativeRustcVmArm.Arrays.PaddingWeight

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.PaddingWeight

@[expose] public section

/-- At the entry: the frame. -/
def entryS : SState := init [(112, true)] (.ptr 0 112)
/-- Registers only. -/
def regsS : SState := init [] .sp
/-- At `.LPaddingWeight_4`: the frame. -/
def exitS : SState := init [(112, true)] (.ptr 0 0)

/-- The prologue's slots, `|point|` (X1) at 8. -/
def slots : List (Nat × XReg) :=
  [(8, .X1), (16, .X29), (24, .X30), (32, .X28), (40, .X27), (48, .X26), (56, .X25), (64, .X24),
    (72, .X23), (80, .X22), (88, .X21), (96, .X20), (104, .X19)]

/-- The registers the loop keeps. -/
def keptRegs : List XReg := calleeRegs.filter fun r ↦ !inSlots slots r

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b6 := exec b6 (after b0 entryS)
sym_block run_b2 := exec b2 (ldS .X22 0)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b7 := exec b7 exitS

public theorem b1_frame : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b1 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b6_frame : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b6 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b6 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (∀ r ∈ calleeRegs, inSlots slots r = false →
      (after b6 (after b0 entryS)).reg r = some (.reg r)) := by
  decide +kernel

public theorem b2_facts : keepsAll (ldS .X22 0) (after b2 (ldS .X22 0)) keptRegs = true ∧
    ([XReg.X19, .X21, .X23, .X29].all fun q ↦ ((ldS .X22 0).reg q).isSome &&
      (after b2 (ldS .X22 0)).reg q == (ldS .X22 0).reg q) = true := by
  decide +kernel
public theorem b3_keeps : keepsAll regsS (after b3 regsS) keptRegs = true := by decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) keptRegs = true := by decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) keptRegs = true := by decide +kernel
public theorem b7_restores : restores slots 112 (after b7 exitS) = true := by decide +kernel

end NativeRustcVmArm.Arrays.PaddingWeight
