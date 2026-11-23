module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.PaddingWeight
public meta import NativeRustcVmX64.Code.Vm.PaddingWeight
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `padding_weight`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 112`, `Field.midS 112`): the 48 bytes of pushes, the 56-byte
frame (`|point|` at offset `16`, the point's end at `24`, `n` at `32`, the first product at `40`,
`48`, the next index at `56`), the call's return-address slot below, the return address above.
- `entryS` at the entry (`b0`, then `b1` or `b6`);
- `rS` at the loop head `NativeRustcVmX64.Vm.PaddingWeight.label_3` (`b2`, loading a coordinate at R13, region 1, and
  calling `EW::mul`);
- `Field.midS 112` at the second call (`b3`), the loop's end (`b4`) and the epilogue (`b7`,
  ending in a jump to `EW::mul`);
- `regsS` at `b5`.
-/

namespace NativeRustcVmX64.Arrays.PaddingWeight

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.PaddingWeight NativeRustcVmX64.Field

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 112
/-- At the loop head: the frame, the coordinate at R13. -/
def rS : SState := elemS 112 (.reg .r13) 0
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(104, .rbp), (96, .r15), (88, .r14), (80, .r13), (72, .r12), (64, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b6 := exec b6 (after b0 entryS)
sym_block run_b2 := exec b2 rS
sym_block run_b3 := exec b3 (midS 112)
sym_block run_b4 := exec b4 (midS 112)
sym_block run_b5 := exec b5 regsS
sym_block run_b7 := exec b7 (midS 112)


/-- What the prologue and `b1` leave: the pushes, `|point|`, the end and `n` in the frame. -/
public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b1 (after b0 entryS)).mem = some (.reg .rsi, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b1 (after b0 entryS)).mem =
      some (.bin .add .W64 (.reg .rdi) (.bin .shl .W64 (.reg .rsi) (.lit 4)), i)) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b1 (after b0 entryS)).mem = some (.reg .rdx, i)) := by
  decide +kernel

/-- What the prologue and `b6` leave. -/
public theorem b6_entry : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b6 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b6 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b6 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (after b6 (after b0 entryS)).reg .rsp = some (.ptr 0 8) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b6 (after b0 entryS)).mem = some (.reg .rsi, i)) := by
  decide +kernel

public theorem b2_call : keepsRegs rS (after b2 rS) (freeRegs slots) = true ∧
    (after b2 rS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b2 rS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ i < 8, findWrite 0 (56 + i) (after b2 rS).mem =
      some (.bin .add .W64 (.reg .rcx) (.lit 1), i)) ∧
    firstOverlap 0 16 8 (after b2 rS).mem = none ∧ firstOverlap 0 24 8 (after b2 rS).mem = none ∧
    firstOverlap 0 32 8 (after b2 rS).mem = none := by
  decide +kernel

public theorem b3_call : keepsRegs (midS 112) (after b3 (midS 112)) (freeRegs slots) = true ∧
    (after b3 (midS 112)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b3 (midS 112)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b3 (midS 112)).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 0 (48 + i) (after b3 (midS 112)).mem = some (.reg .rdx, i)) ∧
    firstOverlap 0 16 8 (after b3 (midS 112)).mem = none ∧
    firstOverlap 0 24 8 (after b3 (midS 112)).mem = none ∧
    firstOverlap 0 32 8 (after b3 (midS 112)).mem = none ∧
    firstOverlap 0 56 8 (after b3 (midS 112)).mem = none := by
  decide +kernel

public theorem b4_keeps : keepsAll (midS 112) (after b4 (midS 112)) (freeRegs slots) = true := by
  decide +kernel
public theorem b5_keeps : keepsAll regsS (after b5 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b7_tail : restoredRegs slots (after b7 (midS 112)) = true ∧
    (after b7 (midS 112)).reg .rsp = some (.ptr 0 112) ∧ (after b7 (midS 112)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 64 ≤ p.1 ∧ p.1 + 8 ≤ 112 := by decide

end NativeRustcVmX64.Arrays.PaddingWeight
