module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove
public meta import NativeRustcVmX64.Code.Vm.EqEvalFnOfEqAbove
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `eq_eval_fn`'s blocks (`eq_above`'s closure), run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the 40 bytes of pushes, the call's
return-address slot below them, the return address above.
- `entryS` at the entry (`b0`, then `b1` or `b5`);
- the loop head `NativeRustcVmX64.Vm.EqEvalFnOfEqAbove.label_3` (`b2`) in three parts: `p1` loads `right[i]`'s limb `1`
  (`rS`: region 1 the element, RBX its address plus 8); `p2` executes raw `bt` without touching
  memory; `p3` reads the carry, limb `0` and calls `EW::mul` (`rS`);
- `regsS` after the call (`b3`, `b4`): no region;
- `Field.midS 48` at the epilogue (`b6`).
-/

namespace NativeRustcVmX64.Arrays.EqEvalFn

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqEvalFnOfEqAbove NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48
/-- At a part reading `right[i]`, RBX its address plus 8. -/
def rS : SState := elemS 48 (.reg .rbx) 8
/-- Registers only. -/
def regsS : SState := init []

/-- The loop head's first part. -/
def p1 : List Directive := b2.take 4
/-- The raw `bt`. -/
def p2 : List Directive := (b2.drop 4).take 1
/-- The rest, to the call. -/
def p3 : List Directive := b2.drop 5

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b5 := exec b5 (after b0 entryS)
sym_block run_p1 := exec p1 rS
sym_block run_p2 := exec p2 regsS
sym_block run_p3 := exec p3 rS
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

public theorem p1_keeps : keepsAll rS (after p1 rS) (freeRegs slots) = true := by decide +kernel

public theorem p2_keeps : keepsAll regsS (after p2 regsS) (freeRegs slots) = true ∧
    (∀ r ∈ [Reg64.rax, .rcx, .rdx, .rbx, .rsi, .r8, .r12, .r14, .r15],
      (after p2 regsS).reg r = some (.reg r)) ∧
    (after p2 regsS).flags.cf = some (.cmp .bit .W64 (.reg .r14) (.reg .rsi)) := by
  decide +kernel

public theorem p3_call : keepsRegs rS (after p3 rS) (freeRegs slots) = true ∧
    (after p3 rS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after p3 rS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b3_keeps : keepsAll regsS (after b3 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b4_keeps : keepsAll regsS (after b4 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b6_restores : restores slots 48 (after b6 (midS 48)) = true ∧
    (after b6 (midS 48)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide


end NativeRustcVmX64.Arrays.EqEvalFn
