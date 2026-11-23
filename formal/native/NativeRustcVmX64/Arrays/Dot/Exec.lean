module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.Dot
public meta import NativeRustcVmX64.Code.Vm.Dot
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `dot`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 64`, `Field.midS 64`): the 56 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1` or `b5`);
- `ldS`/`rdS` at the loop head `NativeRustcVmX64.Vm.Dot.label_3` (`b2`, split after its loads of `left[i]`: `b2a`, then
  `b2b` loads `right[i]` and calls `EW::mul`): region 1 the element, at `r15 + rbp`, `rbx + rbp`;
- `regsS` after the call (`b3`, `b4`): no region;
- `Field.midS 64` at the epilogue (`b6`).
-/

namespace NativeRustcVmX64.Arrays.Dot

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Dot NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 64
/-- At the loop head: the frame, `left[i]` at `r15 + rbp`. -/
def ldS : SState := init [72, 16] [(.rsp, .ptr 0 8)] [] []
  [(.bin .add .W64 (.reg .r15) (.reg .rbp), 1, 0)]
/-- After `left[i]`'s loads: the frame, `right[i]` at `rbx + rbp`. -/
def rdS : SState := init [72, 16] [(.rsp, .ptr 0 8)] [] []
  [(.bin .add .W64 (.reg .rbx) (.reg .rbp), 1, 0)]
/-- Registers only. -/
def regsS : SState := init []

/-- The loop head's loads of `left[i]`. -/
def b2a : List Directive := b2.take 3
/-- The loads of `right[i]` and the call. -/
def b2b : List Directive := b2.drop 3

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(56, .rbp), (48, .r15), (40, .r14), (32, .r13), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_b2a := exec b2a ldS
sym_block run_b2b := exec b2b rdS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b6 := exec b6 (midS 64)

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b5_entry : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b5 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b5 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b5 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b5 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b2a_keeps : keepsAll ldS (after b2a ldS) (freeRegs slots) = true := by
  decide +kernel

public theorem b2b_call : keepsRegs rdS (after b2b rdS) (freeRegs slots) = true ∧
    (after b2b rdS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b2b rdS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b3_keeps : keepsAll regsS (after b3 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b4_keeps : keepsAll regsS (after b4 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b6_restores : restores slots 64 (after b6 (midS 64)) = true ∧
    (after b6 (midS 64)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by decide

end NativeRustcVmX64.Arrays.Dot
