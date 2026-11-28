module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.FormBufAddScaled
public meta import NativeRustcVmX64.Code.Vm.FormBufAddScaled
public meta import NativeRustcVmX64.Layout.Common

/-!
# `FormBuf::add_scaled`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 48`, `Field.midS 48`): the five pushes (offsets `8`-`48`),
the call's return-address slot at `0`, the return address above.
- `entryS` at the entry: `b0`, then `b1` the prologue or `b7` (no terms, `1`);
- `termS` at the loop head `.L4` (`b2`): the frame, term `i` (region 1, R15), the call of
  `EW::mul`;
- `Field.midS 48` at the call of `add_term` (`b3`) and the epilogue (`b6`);
- `regsS` at `b4`, `b5`.
-/

namespace NativeRustcVmX64.Layout.FormBufAddScaled

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormBufAddScaled NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (after freeRegs keepsAll keepsRegs restores)

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 48
/-- At `.L4`: the frame, term `i` (region 1, R15). -/
def termS : SState := init [56, 40] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]
/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(40, .r15), (32, .r14), (24, .r13), (16, .r12), (8, .rbx)]

/-- `b1`'s R13: `40` times the count, less `40`. -/
def r13S : Sym :=
  .bin .add .W64 (.lit 18446744073709551576) (.bin .add .W64 (.bin .shl .W64 (.reg .rdx) (.lit 3))
    (.bin .mul .W64 (.bin .shl .W64 (.reg .rdx) (.lit 3)) (.lit 4)))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b7 := exec b7 (after b0 entryS)
sym_block run_b2 := exec b2 termS
sym_block run_b3 := exec b3 (midS 48)
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 regsS
sym_block run_b6 := exec b6 (midS 48)

public theorem b1_entry : (∀ p ∈ slots, p.1 + 8 ≤ 48 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 entryS)).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b1 (after b0 entryS)).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b1 (after b0 entryS)).reg .rsp = some (.ptr 0 8) ∧
    (after b1 (after b0 entryS)).reg .rbx = some (.reg .r8) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .r15 = some (.reg .rsi) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.reg .rdi) ∧
    (after b1 (after b0 entryS)).reg .r13 = some r13S := by
  decide +kernel

public theorem b7_ret : (after b7 (after b0 entryS)).reg .rsp = some (.ptr 0 ((48 + 8 : Nat) : Int)) ∧
    keeps (frameS 48) (after b7 (after b0 entryS)) = true ∧ (after b7 (after b0 entryS)).mem = [] ∧
    (after b7 (after b0 entryS)).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) := by
  decide +kernel

public theorem b2_call : keepsRegs termS (after b2 termS) (freeRegs slots) = true ∧
    keepsRegs termS (after b2 termS) [.rbx, .r12, .r13, .r14, .r15] = true ∧
    (after b2 termS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b2 termS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 termS).reg .rdi = some (.reg .r14) ∧ (after b2 termS).reg .rsi = some (.reg .rbx) ∧
    (after b2 termS).reg .rdx = some (.load 1 24 8) ∧
    (after b2 termS).reg .rcx = some (.load 1 (24 + 8) 8) := by
  decide +kernel

public theorem b3_call : keepsRegs (midS 48) (after b3 (midS 48)) (freeRegs slots) = true ∧
    keepsRegs (midS 48) (after b3 (midS 48)) [.rbx, .r12, .r13, .r14, .r15] = true ∧
    (after b3 (midS 48)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b3 (midS 48)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 (midS 48)).reg .rdi = some (.reg .r12) ∧
    (after b3 (midS 48)).reg .rsi = some (.reg .r15) ∧
    (after b3 (midS 48)).reg .rdx = some (.reg .rax) ∧
    (after b3 (midS 48)).reg .rcx = some (.reg .rdx) := by
  decide +kernel

public theorem b4_facts : keepsAll regsS (after b4 regsS) (freeRegs slots) = true ∧
    keepsRegs regsS (after b4 regsS) [.rax, .rbx, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem b5_facts : keepsAll regsS (after b5 regsS) (freeRegs slots) = true ∧
    keepsRegs regsS (after b5 regsS) [.rax, .rbx, .r12, .r14] = true ∧
    (after b5 regsS).reg .r15 = some (.bin .add .W64 (.lit 40) (.reg .r15)) ∧
    (after b5 regsS).reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 18446744073709551576)) := by
  decide +kernel

public theorem b6_restores : restores slots 48 (after b6 (midS 48)) = true ∧
    (after b6 (midS 48)).mem = [] ∧ (after b6 (midS 48)).reg .rax = some (.reg .rax) := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 8 ≤ p.1 ∧ p.1 + 8 ≤ 48 := by decide

end NativeRustcVmX64.Layout.FormBufAddScaled
