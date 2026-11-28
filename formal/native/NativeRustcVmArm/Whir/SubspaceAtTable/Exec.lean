module

public import NativeRustcVmArm.Whir.MathFrame
public import NativeRustcVmArm.Code.Vm.SubspaceAtTable
public meta import NativeRustcVmArm.Code.Vm.SubspaceAtTable
public meta import NativeRustcVmArm.Whir.Common

/-!
# `subspace_at_table`'s blocks, run by the symbolic executor

- `b0` from the entry (`entryS`: region 0 the 336-byte frame below SP): the prologue, `memset` of
  the `what` buffer's items;
- `b1`, `b2` (`regsS`, no region): the count test, the loop's registers;
- the loop: `b3` (`ldS`: region 0 the table's pair X25 − 8 points to) loads a pair and calls
  `kmul`; `b4` (`stS`: region 0 the slot X21 points to) stores `What_i`, calls `kmul`; `b5`, `b6`
  (`regsS`): the next `W`, the counters;
- `b7` (`exitS`: region 0 the frame from SP) stores the count and calls `memcpy`; `b8` the
  epilogue.
-/

namespace NativeRustcVmArm.Whir.SubspaceAtTable

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SubspaceAtTable

@[expose] public section

/-- At the entry: the frame below SP (region 0). -/
def entryS : SState := init [(336, true)] (.ptr 0 336)
/-- No region. -/
def regsS : SState := init [] .sp
/-- The pair X25 − 8 points to (region 0). -/
def ldS : SState := init [(16, false)] .sp [(.X25, .ptr 0 8)]
/-- The slot X21 points to (region 0). -/
def stS : SState := init [(8, false)] .sp [(.X21, .ptr 0 0)]
/-- The frame from SP (region 0). -/
def exitS : SState := init [(336, true)] (.ptr 0 0)

/-- The prologue's slots. -/
def slots : List (Nat × XReg) :=
  [(256, .X29), (264, .X30), (272, .X26), (280, .X25), (288, .X24), (296, .X23), (304, .X22),
    (312, .X21), (320, .X20), (328, .X19)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 ldS
sym_block run_b4 := exec b4 stS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 exitS
sym_block run_b8 := exec b8 exitS

public theorem b0_frame : (∀ p ∈ slots, p.1 + 8 ≤ 336 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 336) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b1_keeps : keepsRegs regsS (after b1 regsS) (freeRegs slots) = true ∧
    (after b1 regsS).mem = [] := by decide +kernel
public theorem b2_keeps : keepsRegs regsS (after b2 regsS) (freeRegs slots) = true ∧
    (after b2 regsS).mem = [] := by decide +kernel
public theorem b3_keeps : keepsRegs ldS (after b3 ldS) (freeRegs slots) = true ∧
    (after b3 ldS).mem = [] := by decide +kernel
public theorem b4_keeps : keepsRegs stS (after b4 stS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b4 stS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b5_keeps : keepsRegs regsS (after b5 regsS) (freeRegs slots) = true ∧
    (after b5 regsS).mem = [] := by decide +kernel
public theorem b6_keeps : keepsRegs regsS (after b6 regsS) (freeRegs slots) = true ∧
    (after b6 regsS).mem = [] := by decide +kernel
public theorem b7_keeps : keepsRegs exitS (after b7 exitS) (freeRegs slots) = true ∧
    ∀ w ∈ (after b7 exitS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by decide +kernel
public theorem b8_restores : restores slots 336 (after b8 exitS) = true ∧
    (after b8 exitS).mem = [] := by decide +kernel

end NativeRustcVmArm.Whir.SubspaceAtTable
