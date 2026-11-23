module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.Powers
public meta import NativeRustcVmX64.Code.Vm.Powers
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `powers`' blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the 40 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1`, or `b5` returning at once);
- the loop head `NativeRustcVmX64.Vm.Powers.label_2` (`b2`) in two parts: `s1` stores the power in `out[i]` (`stS`:
  region 1 the element, at R14), `s2` calls `EW::mul` (`Field.midS 48`);
- `regsS` after the call (`b3`): no region;
- `Field.midS 48` at the epilogue (`b4`, `b5`, as one run `b45`).
-/

namespace NativeRustcVmX64.Arrays.Powers

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Powers NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48
/-- At the stores: the frame, `out[i]` at R14. -/
def stS : SState := elemS 48 (.reg .r14) 0
/-- Registers only. -/
def regsS : SState := init []

/-- The loop head's stores. -/
def s1 : List Directive := b2.take 3
/-- The loop head's call. -/
def s2 : List Directive := b2.drop 3
/-- The epilogue and the return. -/
def b45 : List Directive := b4 ++ b5

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_s1 := exec s1 stS
sym_block run_s2 := exec s2 (midS 48)
sym_block run_b3 := exec b3 regsS
sym_block run_b45 := exec b45 (midS 48)

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b5_leaf : keeps entryS (after b5 (after b0 entryS)) = true ∧
    (after b5 (after b0 entryS)).mem = [] ∧
    (after b5 (after b0 entryS)).reg .rsp = some (.ptr 0 ((48 + 8 : Nat) : Int)) := by
  decide +kernel

public theorem s1_store : keepsRegs stS (after s1 stS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after s1 stS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after s1 stS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after s1 stS).mem = some (.reg .rdx, i)) := by
  decide +kernel

public theorem s2_call : keepsRegs (midS 48) (after s2 (midS 48)) (freeRegs slots) = true ∧
    (after s2 (midS 48)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after s2 (midS 48)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b3_keeps : keepsAll regsS (after b3 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b45_restores : restores slots 48 (after b45 (midS 48)) = true ∧
    (after b45 (midS 48)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide


end NativeRustcVmX64.Arrays.Powers
