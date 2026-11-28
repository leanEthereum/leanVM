module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets
public meta import NativeRustcVmX64.Code.Vm.InsertionSortOfStackOffsets
public meta import NativeRustcVmX64.Layout.Common

/-!
# `insertion_sort`'s blocks, run by the symbolic executor (x86-64)

Region 0 of every environment is the frame: the two pushes (`16` bytes, RSP at offset `0` in the
body) and the return address above. Then:
- `entryS` (`b0`, `b1`, `b22` without pushes): the frame, RSP at offset `16`;
- `regsS`: the frame alone (`b3`, `b4`, `b8`, `b10`, `b12`, `b14`, `b16`, `b17`, `b19`, `b20`,
  `b21` with `b22`);
- `ordS x`: `order[x]` (region 1, at `RDI + 8 x`: `b5` with R8, `b6` with R10);
- `szS x`: `sizes[x]` (region 1, at `RDX + 8 x`: `b7`, `b13` with R11, `b11` with R9);
- `swapS`: `order[r10]`, `order[r10 + 1]` (region 1, at `RDI + 8 R10`: `b18`).
-/

namespace NativeRustcVmX64.Layout.InsertionSort

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InsertionSortOfStackOffsets
open NativeRustcVmX64.Transcript (after after_eq exec_after EpiOk MidOk ProOk)
open NativeRustcVmX64.Field (frameS)

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 16
/-- The body without memory but the frame, RSP at offset `0`. -/
def regsS : SState := init [24] [(.rsp, .ptr 0 0)]
/-- `(p, x, 8)`'s address. -/
def addr (p x : Reg64) : Sym := .bin .add .W64 (.reg p) (.bin .mul .W64 (.reg x) (.lit 8))
/-- `order[x]`. -/
def ordS (x : Reg64) : SState := init [24, 8] [(.rsp, .ptr 0 0)] [] [] [(addr .rdi x, 1, 0)]
/-- `sizes[x]`. -/
def szS (x : Reg64) : SState := init [24, 8] [(.rsp, .ptr 0 0)] [] [] [(addr .rdx x, 1, 0)]
/-- `order[r10]`, `order[r10 + 1]`. -/
def swapS : SState := init [24, 16] [(.rsp, .ptr 0 0)] [] [] [(addr .rdi .r10, 1, 0)]

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(8, .r14), (0, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b22e := exec b22 (after b0 entryS)
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b3 := exec b3 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 (ordS .r8)
sym_block run_b6 := exec b6 (ordS .r10)
sym_block run_b7 := exec b7 (szS .r11)
sym_block run_b8 := exec b8 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 (szS .r9)
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 (szS .r11)
sym_block run_b14 := exec b14 regsS
sym_block run_b16 := exec b16 regsS
sym_block run_b17 := exec b17 regsS
sym_block run_b18 := exec b18 swapS
sym_block run_b19 := exec b19 regsS
sym_block run_b20 := exec b20 regsS
sym_block run_b21 := exec b21 regsS
sym_block run_b22 := exec b22 (after b21 regsS)

/-- A body block: the frame kept, nothing written. -/
@[expose] public def Quiet (S : SState) : Prop := MidOk 16 0 slots S = true ∧ S.mem = []

/-- The arguments. -/
@[expose] public def kA : List Reg64 := [.rdi, .rsi, .rdx, .rcx]
/-- The arguments and the outer loop's counters. -/
@[expose] public def kB : List Reg64 := kA ++ [.r8, .rax]
/-- And the comparison's operands. -/
@[expose] public def kC : List Reg64 := kB ++ [.r9, .r10, .r11]

public theorem b0_facts : keeps entryS (after b0 entryS) = true ∧ (after b0 entryS).mem = [] ∧
    Arrays.keepsRegs entryS (after b0 entryS) kA = true ∧
    (after b0 entryS).flags.zf = some (.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)) := by
  decide +kernel

public theorem b22e_facts : (after b22 (after b0 entryS)).reg .rsp = some (.ptr 0 ((16 + 8 : Nat) : Int)) ∧
    keeps (frameS 16) (after b22 (after b0 entryS)) = true ∧ (after b22 (after b0 entryS)).mem = [] := by
  decide +kernel

public theorem b1_facts : ProOk 16 0 slots (after b1 (after b0 entryS)) = true ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    Arrays.keepsRegs entryS (after b1 (after b0 entryS)) kA = true ∧
    (after b1 (after b0 entryS)).reg .rax = some (.lit 18446744073709551615) ∧
    (after b1 (after b0 entryS)).reg .r8 = some (.lit 0) := by
  decide +kernel

public theorem b3_facts : Quiet (after b3 regsS) ∧ Arrays.keepsRegs regsS (after b3 regsS) kA = true ∧
    (after b3 regsS).reg .r8 = some (.bin .add .W64 (.reg .r8) (.lit 1)) ∧
    (after b3 regsS).reg .rax = some (.bin .add .W64 (.reg .rax) (.lit 1)) ∧
    (after b3 regsS).flags.zf = some (.cmp .eq .W64 (.bin .add .W64 (.reg .r8) (.lit 1)) (.reg .rsi)) := by
  unfold Quiet; decide +kernel

public theorem b4_facts : Quiet (after b4 regsS) ∧ Arrays.keepsRegs regsS (after b4 regsS) kB = true ∧
    (after b4 regsS).flags.zf = some (.cmp .eq .W64 (.bin .and .W64 (.reg .r8) (.reg .r8)) (.lit 0)) := by
  unfold Quiet; decide +kernel

public theorem b5_facts : Quiet (after b5 (ordS .r8)) ∧
    Arrays.keepsRegs (ordS .r8) (after b5 (ordS .r8)) kB = true ∧
    (after b5 (ordS .r8)).reg .r9 = some (.load 1 0 8) ∧
    (after b5 (ordS .r8)).reg .r10 = some (.reg .rax) := by
  unfold Quiet; decide +kernel

public theorem b6_facts : Quiet (after b6 (ordS .r10)) ∧
    Arrays.keepsRegs (ordS .r10) (after b6 (ordS .r10)) (kB ++ [.r9, .r10]) = true ∧
    (after b6 (ordS .r10)).reg .r11 = some (.load 1 0 8) ∧
    (after b6 (ordS .r10)).flags.cf = some (.cmp .ult .W64 (.load 1 0 8) (.reg .rcx)) := by
  unfold Quiet; decide +kernel

public theorem b7_facts : Quiet (after b7 (szS .r11)) ∧
    Arrays.keepsRegs (szS .r11) (after b7 (szS .r11)) kC = true ∧
    (after b7 (szS .r11)).reg .r14 = some (.load 1 0 8) ∧
    (after b7 (szS .r11)).flags.cf = some (.cmp .ult .W64 (.reg .r9) (.reg .rcx)) := by
  unfold Quiet; decide +kernel

public theorem b8_facts : Quiet (after b8 regsS) ∧
    Arrays.keepsRegs regsS (after b8 regsS) kC = true ∧
    (after b8 regsS).reg .rbx = some (.lit 0) := by
  unfold Quiet; decide +kernel

public theorem b10_facts : Quiet (after b10 regsS) ∧
    Arrays.keepsRegs regsS (after b10 regsS) kC = true ∧
    (after b10 regsS).reg .r14 = some (.lit 0) ∧
    (after b10 regsS).flags.cf = some (.cmp .ult .W64 (.reg .r9) (.reg .rcx)) := by
  unfold Quiet; decide +kernel

public theorem b11_facts : Quiet (after b11 (szS .r9)) ∧
    Arrays.keepsRegs (szS .r9) (after b11 (szS .r9)) (kC ++ [.r14]) = true ∧
    (after b11 (szS .r9)).reg .rbx = some (.load 1 0 8) ∧
    (after b11 (szS .r9)).flags.cf = some (.cmp .ult .W64 (.reg .r14) (.load 1 0 8)) := by
  unfold Quiet; decide +kernel

public theorem b12_facts : Quiet (after b12 regsS) ∧
    Arrays.keepsRegs regsS (after b12 regsS) (kC ++ [.rbx]) = true ∧
    (after b12 regsS).flags.cf = some (.cmp .ult .W64 (.reg .r11) (.reg .rcx)) := by
  unfold Quiet; decide +kernel

public theorem b13_facts : Quiet (after b13 (szS .r11)) ∧
    Arrays.keepsRegs (szS .r11) (after b13 (szS .r11)) (kC ++ [.rbx]) = true ∧
    (after b13 (szS .r11)).reg .r14 = some (.load 1 0 8) ∧
    (after b13 (szS .r11)).flags.cf = some (.cmp .ult .W64 (.reg .r9) (.reg .r11)) := by
  unfold Quiet; decide +kernel

public theorem b14_facts : Quiet (after b14 regsS) ∧
    Arrays.keepsRegs regsS (after b14 regsS) kC = true := by
  unfold Quiet; decide +kernel

public theorem b16_facts : Quiet (after b16 regsS) ∧
    Arrays.keepsRegs regsS (after b16 regsS) (kC ++ [.rbx]) = true ∧
    (after b16 regsS).reg .r14 = some (.lit 0) ∧
    (after b16 regsS).flags.cf = some (.cmp .ult .W64 (.reg .r9) (.reg .r11)) := by
  unfold Quiet; decide +kernel

public theorem b17_facts : Quiet (after b17 regsS) ∧
    Arrays.keepsRegs regsS (after b17 regsS) kC = true ∧
    (after b17 regsS).flags.zf = some (.cmp .eq .W64 (.reg .rbx) (.reg .r14)) := by
  unfold Quiet; decide +kernel

public theorem b18_facts : MidOk 16 0 slots (after b18 swapS) = true ∧
    Arrays.keepsRegs swapS (after b18 swapS) (kB ++ [.r9, .r10]) = true ∧
    (∀ w ∈ (after b18 swapS).mem, w.r = 1 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b18 swapS).mem = some (.reg .r9, i)) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b18 swapS).mem = some (.reg .r11, i)) ∧
    (after b18 swapS).reg .r11 = some (.bin .add .W64 (.lit 18446744073709551615) (.reg .r10)) ∧
    (after b18 swapS).flags.cf =
      some (.cmp .addC .W64 (.lit 18446744073709551615) (.reg .r10)) := by
  decide +kernel

public theorem b19_facts : Quiet (after b19 regsS) ∧
    Arrays.keepsRegs regsS (after b19 regsS) (kB ++ [.r9]) = true ∧
    (after b19 regsS).reg .r10 = some (.reg .r11) ∧
    (after b19 regsS).flags.cf = some (.cmp .ult .W64 (.reg .r10) (.reg .rsi)) := by
  unfold Quiet; decide +kernel

public theorem b20_facts : Quiet (after b20 regsS) ∧
    Arrays.keepsRegs regsS (after b20 regsS) kB = true := by
  unfold Quiet; decide +kernel

public theorem b21_facts : EpiOk 16 slots (after b22 (after b21 regsS)) = true ∧
    (after b22 (after b21 regsS)).mem = [] := by
  decide +kernel

public theorem slots_le : ∀ p ∈ slots, p.1 + 8 ≤ 16 := by decide
public theorem slots_cs : ∀ p ∈ slots, calleeSaved p.2 = true := by decide

end NativeRustcVmX64.Layout.InsertionSort
