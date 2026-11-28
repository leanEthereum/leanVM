module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.EqEval
public meta import NativeRustcVmX64.Code.Vm.EqEval
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `eq_eval`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the 40 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1` or `b5`);
- the loop head `NativeRustcVmX64.Vm.EqEval.label_3` (`b2`) in three parts, each reading one slice's element (region 1):
  `p1` loads `left[i]`'s limb `0` (`lS`), `p2` both of `right[i]`'s (`rS`), `p3` `left[i]`'s limb
  `1` and calls `EW::mul` (`lS`);
- `regsS` after the call (`b3`, `b4`): no region;
- `Field.midS 48` at the epilogue (`b6`).
-/

namespace NativeRustcVmX64.Arrays.EqEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqEval NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48
/-- At a part reading `left[i]`, at `r15 + r12`. -/
def lS : SState := elemS 48 (.bin .add .W64 (.reg .r15) (.reg .r12)) 0
/-- At a part reading `right[i]`, at `rbx + r12`. -/
def rS : SState := elemS 48 (.bin .add .W64 (.reg .rbx) (.reg .r12)) 0
/-- Registers only. -/
def regsS : SState := init []

/-- The loop head's first part. -/
def p1 : List Directive := b2.take 2
/-- The second part. -/
def p2 : List Directive := (b2.drop 2).take 2
/-- The third part, to the call. -/
def p3 : List Directive := b2.drop 4

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_p1 := exec p1 lS
sym_block run_p2 := exec p2 rS
sym_block run_p3 := exec p3 lS
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b6 := exec b6 (midS 48)

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem b5_entry : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b5 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b5 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b5 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b5 (after b0 entryS)).reg .rsp = some (.ptr 0 8) := by
  decide +kernel

public theorem p1_keeps : keepsAll lS (after p1 lS) (freeRegs slots) = true := by decide +kernel
public theorem p2_keeps : keepsAll rS (after p2 rS) (freeRegs slots) = true := by decide +kernel

public theorem p3_call : keepsRegs lS (after p3 lS) (freeRegs slots) = true ∧
    (after p3 lS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after p3 lS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b3_keeps : keepsAll regsS (after b3 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b6_restores : restores slots 48 (after b6 (midS 48)) = true ∧
    (after b6 (midS 48)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide


end NativeRustcVmX64.Arrays.EqEval
