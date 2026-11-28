module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.IndexMleFrom
public meta import NativeRustcVmX64.Code.Vm.IndexMleFrom
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `index_mle_from`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 64`, `Field.midS 64`): the 56 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1` or `b7`);
- `rS` at the loop head `NativeRustcVmX64.Vm.IndexMleFrom.label_3` (`b2`, loading a coordinate at R14, region 1, and
  calling `EW::mul`);
- `Field.midS 64` at the next two calls (`b3`, `b4`) and the epilogue (`b8`);
- `regsS` after the last call (`b5`, `b6`): no region.
-/

namespace NativeRustcVmX64.Arrays.IndexMleFrom

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.IndexMleFrom NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 64
/-- At the loop head: the frame, the coordinate at R14. -/
def rS : SState := elemS 64 (.reg .r14) 0
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(56, .rbp), (48, .r15), (40, .r14), (32, .r13), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b7 := exec b7 (after b0 entryS)
sym_block run_b2 := exec b2 rS
sym_block run_b3 := exec b3 (midS 64)
sym_block run_b4 := exec b4 (midS 64)
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 regsS
sym_block run_b8 := exec b8 (midS 64)

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b7_entry : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b7 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b7 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b7 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b7 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b2_call : keepsRegs rS (after b2 rS) (freeRegs slots) = true ∧
    (after b2 rS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b2 rS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b3_call : keepsRegs (midS 64) (after b3 (midS 64)) (freeRegs slots) = true ∧
    (after b3 (midS 64)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b3 (midS 64)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b4_call : keepsRegs (midS 64) (after b4 (midS 64)) (freeRegs slots) = true ∧
    (after b4 (midS 64)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b4 (midS 64)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b5_keeps : keepsAll regsS (after b5 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b6_keeps : keepsAll regsS (after b6 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b8_restores : restores slots 64 (after b8 (midS 64)) = true ∧
    (after b8 (midS 64)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by decide


end NativeRustcVmX64.Arrays.IndexMleFrom
