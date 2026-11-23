module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.ProdE
public meta import NativeRustcVmX64.Code.Vm.ProdE
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `prod_e`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 32`, `Field.midS 32`): the 24 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`);
- `lS` at the loop head `NativeRustcVmX64.Vm.ProdE.label_1` (`b1`): reads `values[i]` (region 1, at R14 + R15) and calls
  `EW::mul`;
- `regsS` after the call (`b2`): no region;
- `Field.midS 32` at the epilogue (`b3`).
-/

namespace NativeRustcVmX64.Arrays.ProdE

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ProdE NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 32
/-- At the loop head, reading `values[i]` at `r14 + r15`. -/
def lS : SState := elemS 32 (.bin .add .W64 (.reg .r14) (.reg .r15)) 0
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(24, .r15), (16, .r14), (8, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 lS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 (midS 32)

public theorem b0_entry : (∀ p ∈ slots, p.1 + 8 ≤ 32 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (after b0 entryS).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b1_call : keepsRegs lS (after b1 lS) (freeRegs slots) = true ∧
    (after b1 lS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b1 lS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b2_keeps : keepsAll regsS (after b2 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b3_restores : restores slots 32 (after b3 (midS 32)) = true ∧
    (after b3 (midS 32)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 32 := by decide

end NativeRustcVmX64.Arrays.ProdE
