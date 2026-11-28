module

public import NativeRustcVmX64.Arrays.Common
public import NativeRustcVmX64.Code.Vm.EqKernel
public meta import NativeRustcVmX64.Code.Vm.EqKernel
public meta import NativeRustcVmX64.Arrays.Common

/-!
# `eq_kernel`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 112`, `Field.midS 112`): the call's return-address slot at
offset 0, the locals at 8-63 (the coordinate's address 8, the size 16, the half 24, `point`'s end
32, `|out|` 40, the coordinate's limbs 48, 56), the six pushes at 64-111, the return address.
- `Field.frameS 112` at the entry (`b0`, `b1`);
- `outS` at `NativeRustcVmX64.Vm.EqKernel.label_2` (`b2`): region 1 `out[0]`, R15 its address;
- `Field.midS 112` for the blocks touching the frame only (`b3`, `b5`, `b7`, `b12`, `b13`, `b14`);
- `regsS` for `b6`, `b11`;
- `ptS` for `b8`: region 1 the coordinate, its address the frame's word at 8;
- `mulS` for `b9`: region 1 `out[j]`, R15 + RBX its address plus 8; the call of `EW::mul`;
- `storeS` for `b10`: also region 2 `out[2^i + j]`, R12 + RBX its address plus 8.
-/

namespace NativeRustcVmX64.Arrays.EqKernel

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.EqKernel NativeRustcVmX64.Field

@[expose] public section

/-- At `b2`: region 1 `out[0]`, R15 its address. -/
def outS : SState := elemS 112 (.reg .r15) 0
/-- Registers only. -/
def regsS : SState := init []
/-- At `b8`: region 1 the coordinate, at the frame's word 8. -/
def ptS : SState := elemS 112 (.load 0 8 8) 0
/-- At `b9`: region 1 `out[j]`, R15 + RBX its address plus 8. -/
def mulS : SState := elemS 112 (.bin .add .W64 (.reg .r15) (.reg .rbx)) 8
/-- At `b10`: region 1 `out[j]` (R15 + RBX plus 8), region 2 `out[2^i + j]` (R12 + RBX plus 8). -/
def storeS : SState := init [120, 16, 16] [(.rsp, .ptr 0 8)] [] []
  [(.bin .add .W64 (.reg .r15) (.reg .rbx), 1, 8), (.bin .add .W64 (.reg .r12) (.reg .rbx), 2, 8)]

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(104, .rbp), (96, .r15), (88, .r14), (80, .r13), (72, .r12), (64, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 (frameS 112)
sym_block run_b1 := exec b1 (after b0 (frameS 112))
sym_block run_b2 := exec b2 outS
sym_block run_b3 := exec b3 (midS 112)
sym_block run_b5 := exec b5 (midS 112)
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 (midS 112)
sym_block run_b8 := exec b8 ptS
sym_block run_b9 := exec b9 mulS
sym_block run_b10 := exec b10 storeS
sym_block run_b11 := exec b11 regsS
sym_block run_b1314 := exec (b13 ++ b14) (midS 112)
sym_block run_b14 := exec b14 (midS 112)

public theorem b0_facts : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0 (frameS 112)).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b0 (frameS 112)).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (after b0 (frameS 112)).reg .rsp = some (.ptr 0 8) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b0 (frameS 112)).mem = some (.reg .rdi, i)) ∧
    (after b0 (frameS 112)).reg .rax = some (.lit 1) ∧
    (after b0 (frameS 112)).reg .rdx = some (.bin .shl .W64 (.lit 1) (.reg .rsi)) ∧
    (after b0 (frameS 112)).reg .rcx = some (.reg .rsi) ∧
    (after b0 (frameS 112)).reg .r8 = some (.reg .rcx) ∧
    (after b0 (frameS 112)).reg .r15 = some (.reg .rdx) := by
  decide +kernel

public theorem b1_facts : (∀ p ∈ slots, p.1 + 8 ≤ 112 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b1 (after b0 (frameS 112))).mem = some (.reg p.2, i)) ∧
    (∀ w ∈ (after b1 (after b0 (frameS 112))).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (after b1 (after b0 (frameS 112))).reg .rsp = some (.ptr 0 8) ∧
    (after b1 (after b0 (frameS 112))).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem b2_facts : keepsRegs outS (after b2 outS) [.rsp, .rax, .rcx, .rdx, .r8, .r15] = true ∧
    (∀ w ∈ (after b2 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b2 outS).mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b2 outS).mem = some (.lit 0, i)) := by
  decide +kernel

public theorem b3_facts : keepsRegs (midS 112) (after b3 (midS 112)) [.rsp, .r8] = true ∧
    (∀ w ∈ (after b3 (midS 112)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b3 (midS 112)).reg .rdx = some (.lit 1) ∧
    (after b3 (midS 112)).reg .r15 = some (.bin .add .W64 (.lit 8) (.reg .r15)) ∧
    firstOverlap 0 8 8 (after b3 (midS 112)).mem = none ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b3 (midS 112)).mem = some (.reg .rdx, i)) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b3 (midS 112)).mem =
      some (.bin .add .W64 (.load 0 8 8) (.bin .shl .W64 (.reg .rcx) (.lit 4)), i)) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b3 (midS 112)).mem = some (.reg .r8, i)) := by
  decide +kernel

public theorem b5_facts : keepsRegs (midS 112) (after b5 (midS 112)) [.rsp, .r15] = true ∧
    (∀ w ∈ (after b5 (midS 112)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b5 (midS 112)).reg .rdx = some (.bin .add .W64 (.load 0 24 8) (.load 0 24 8)) ∧
    (after b5 (midS 112)).reg .r8 = some (.load 0 40 8) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b5 (midS 112)).mem =
      some (.bin .add .W64 (.lit 16) (.load 0 8 8), i)) ∧
    firstOverlap 0 16 8 (after b5 (midS 112)).mem = none ∧
    firstOverlap 0 32 8 (after b5 (midS 112)).mem = none ∧
    firstOverlap 0 40 8 (after b5 (midS 112)).mem = none := by
  decide +kernel

public theorem b6_keeps : keepsAll regsS (after b6 regsS) [.rax, .rcx, .rdx, .r8, .r15] = true := by
  decide +kernel

public theorem b7_facts : keepsRegs (midS 112) (after b7 (midS 112)) [.rsp, .rdx, .r8, .r15] = true ∧
    (∀ w ∈ (after b7 (midS 112)).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b7 (midS 112)).reg .rbp = some (.ite (.not (.cmp .ult .W64 (.reg .rbp) (.reg .rdx)))
      (.reg .rdx) (.reg .rbp)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b7 (midS 112)).mem = some (.reg .rdx, i)) ∧
    firstOverlap 0 8 8 (after b7 (midS 112)).mem = none ∧
    firstOverlap 0 16 8 (after b7 (midS 112)).mem = none ∧
    firstOverlap 0 32 8 (after b7 (midS 112)).mem = none ∧
    firstOverlap 0 40 8 (after b7 (midS 112)).mem = none := by
  decide +kernel

public theorem b8_facts : keepsRegs ptS (after b8 ptS) [.rsp, .r15] = true ∧
    (∀ w ∈ (after b8 ptS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b8 ptS).reg .rbp = some (.bin .shl .W64 (.reg .rbp) (.lit 4)) ∧
    (after b8 ptS).reg .r12 = some (.bin .add .W64 (.reg .r15)
      (.bin .shl .W64 (.load 0 24 8) (.lit 4))) ∧
    (after b8 ptS).reg .rbx = some (.lit 0) ∧
    (∀ i < 8, findWrite 0 (48 + i) (after b8 ptS).mem = some (.load 1 8 8, i)) ∧
    (∀ i < 8, findWrite 0 (56 + i) (after b8 ptS).mem = some (.load 1 0 8, i)) ∧
    firstOverlap 0 8 8 (after b8 ptS).mem = none ∧
    firstOverlap 0 16 8 (after b8 ptS).mem = none ∧
    firstOverlap 0 24 8 (after b8 ptS).mem = none ∧
    firstOverlap 0 32 8 (after b8 ptS).mem = none ∧
    firstOverlap 0 40 8 (after b8 ptS).mem = none := by
  decide +kernel

public theorem b9_facts : (after b9 mulS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b9 mulS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b9 mulS).reg .rdi = some (.load 1 0 8) ∧ (after b9 mulS).reg .rsi = some (.load 1 8 8) ∧
    (after b9 mulS).reg .rdx = some (.load 0 56 8) ∧ (after b9 mulS).reg .rcx = some (.load 0 48 8) ∧
    (after b9 mulS).reg .r13 = some (.load 1 0 8) ∧ (after b9 mulS).reg .r14 = some (.load 1 8 8) ∧
    keepsRegs mulS (after b9 mulS) [.rbx, .rbp, .r12, .r15] = true := by
  decide +kernel

public theorem b10_facts : keepsRegs storeS (after b10 storeS) [.rsp, .rbp, .r12, .r15] = true ∧
    (after b10 storeS).reg .rbx = some (.bin .add .W64 (.lit 16) (.reg .rbx)) ∧
    (∀ w ∈ (after b10 storeS).mem, (w.r = 1 ∧ w.off + w.n ≤ 16) ∨ (w.r = 2 ∧ w.off + w.n ≤ 16)) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b10 storeS).mem =
      some (.bin .xor .W64 (.reg .r13) (.reg .rax), i)) ∧
    (∀ i < 8, findWrite 1 (0 + 8 + i) (after b10 storeS).mem =
      some (.bin .xor .W64 (.reg .r14) (.reg .rdx), i)) ∧
    (∀ i < 8, findWrite 2 (0 + i) (after b10 storeS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 2 (0 + 8 + i) (after b10 storeS).mem = some (.reg .rdx, i)) := by
  decide +kernel

public theorem b11_keeps : keepsAll regsS (after b11 regsS) [.r15] = true := by decide +kernel

public theorem b1314_facts : restores slots 112 (after (b13 ++ b14) (midS 112)) = true ∧
    (after (b13 ++ b14) (midS 112)).mem = [] ∧
    (after (b13 ++ b14) (midS 112)).reg .rax = some (.lit 1) ∧
    (after (b13 ++ b14) (midS 112)).reg .rdx = some (.load 0 16 8) := by
  decide +kernel

public theorem b14_facts : restores slots 112 (after b14 (midS 112)) = true ∧
    (after b14 (midS 112)).mem = [] ∧
    (after b14 (midS 112)).reg .rax = some (.reg .rax) ∧
    (after b14 (midS 112)).reg .rdx = some (.reg .rdx) := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 64 ≤ p.1 ∧ p.1 + 8 ≤ 112 := by decide

public theorem freeRegs_slots : Arrays.freeRegs slots = [] := by decide

end NativeRustcVmX64.Arrays.EqKernel
