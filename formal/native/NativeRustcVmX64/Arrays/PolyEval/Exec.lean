module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.PolyEval
public meta import NativeRustcVmX64.Code.Vm.PolyEval
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `poly_eval`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 64`, `Field.midS 64`): the 56 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, falling into the loop);
- `cS` at the loop head `NativeRustcVmX64.Vm.PolyEval.label_1` (`b1`, loading a coefficient and calling `EW::mul`):
  region 1 the coefficient, 16 bytes below `r12 + r15`;
- `regsS` after the call (`b2`): no region;
- `Field.midS 64` at the epilogue (`b3`).
-/

namespace NativeRustcVmX64.Arrays.PolyEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PolyEval NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 64
/-- At the loop head: the frame, the coefficient 16 bytes below `r12 + r15`. -/
def cS : SState := elemS 64 (.bin .add .W64 (.reg .r12) (.reg .r15)) 16
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(56, .rbp), (48, .r15), (40, .r14), (32, .r13), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 cS
sym_block run_b2 := exec b2 regsS
sym_block run_b3 := exec b3 (midS 64)

public theorem b0_entry : (∀ p ∈ slots, p.1 + 8 ≤ 64 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0 entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b0 entryS).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b1_call : keepsRegs cS (after b1 cS) (freeRegs slots) = true ∧
    (after b1 cS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b1 cS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b2_keeps : keepsAll regsS (after b2 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b3_restores : restores slots 64 (after b3 (midS 64)) = true ∧
    (after b3 (midS 64)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 64 := by decide


end NativeRustcVmX64.Arrays.PolyEval
