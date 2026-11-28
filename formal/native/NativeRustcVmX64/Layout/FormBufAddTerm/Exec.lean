module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.FormBufAddTerm
public meta import NativeRustcVmX64.Code.Vm.FormBufAddTerm
public meta import NativeRustcVmX64.Layout.Common

/-!
# `FormBuf::add_term`'s blocks, run by the symbolic executor (x86-64)

Region 0 of every environment is the frame: the five pushes (`40` bytes, RSP at offset `0` in
the body) and the return address above. Then:
- `entryS` (`b0`, `b10`, `b1`): the count (region 1, RDI), the term `t` (region 2, RSI);
- `regsS` (`b2`, `b4`, `b6`, `b7`, `b9`, `b12`, `b13`, `b15`, `b16`): the frame alone;
- `degS` (`b5`): term `j` (region 1, R10);
- `colS` (`b8`): term `j`'s columns (region 1, R15 its offset `8`), `t`'s (region 2, R11 its
  offset `8`), the index R12 below `2`;
- `foundS` (`b11`): term `j` (region 1, R10);
- `pushS` (`b14`): the new term (region 1, R8), `t` (region 2, RSI), the count (region 3, RDI).
-/

namespace NativeRustcVmX64.Layout.FormBufAddTerm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FormBufAddTerm
open NativeRustcVmX64.Transcript (after after_eq exec_after EpiOk MidOk ProOk)

@[expose] public section

/-- At the entry: the frame, RSP at offset `40`; the count (RDI); `t` (RSI). -/
def entryS : SState := init [48, 8, 40] [(.rsp, .ptr 0 40), (.rdi, .ptr 1 0), (.rsi, .ptr 2 0)]
/-- The body without memory but the frame, RSP at offset `0`. -/
def regsS : SState := init [48] [(.rsp, .ptr 0 0)]
/-- At `.L5`: term `j` (R10). -/
def degS : SState := init [48, 40] [(.rsp, .ptr 0 0), (.r10, .ptr 1 0)]
/-- At `b8`: term `j`'s columns (R15 at offset `8`), `t`'s (R11 at offset `8`), R12 below `2`. -/
def colS : SState :=
  init [48, 40, 40] [(.rsp, .ptr 0 0), (.r15, .ptr 1 8), (.r11, .ptr 2 8)] [] [(.reg .r12, 2)]
/-- At `.L13`: term `j` (R10). -/
abbrev foundS : SState := degS
/-- At `.L12`: the new term (R8), `t` (RSI), the count (RDI). -/
def pushS : SState :=
  init [48, 40, 40, 8] [(.rsp, .ptr 0 0), (.r8, .ptr 1 0), (.rsi, .ptr 2 0), (.rdi, .ptr 3 0)]

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) := [(32, .r15), (24, .r14), (16, .r13), (8, .r12), (0, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b10 := exec b10 (after b0 entryS)
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 regsS
sym_block run_b4 := exec b4 regsS
sym_block run_b5 := exec b5 degS
sym_block run_b6 := exec b6 regsS
sym_block run_b7 := exec b7 regsS
sym_block run_b8 := exec b8 colS
sym_block run_b9 := exec b9 regsS
sym_block run_b11 := exec b11 foundS
sym_block run_b12 := exec b12 regsS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 pushS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 regsS

/-- The count. -/
@[expose] public def nS : Sym := .load 1 0 8

/-- `b1`'s R8: the count's address plus `8 + 40 n`, the end of the terms. -/
@[expose] public def r8S : Sym :=
  .bin .add .W64 (.lit 8) (.bin .add .W64 (.ptr 1 0)
    (.bin .mul .W64 (.bin .add .W64 nS (.bin .mul .W64 nS (.lit 4))) (.lit 8)))

/-- A body block: the frame kept, nothing written. -/
@[expose] public def Quiet (S : SState) : Prop := MidOk 40 0 slots S = true ∧ S.mem = []

public theorem b0_facts : keeps entryS (after b0 entryS) = true ∧ (after b0 entryS).mem = [] ∧
    (after b0 entryS).flags.cf = some (.cmp .ult .W64 nS (.lit 148)) ∧
    (after b0 entryS).flags.zf = some (.cmp .eq .W64 nS (.lit 148)) := by
  decide +kernel

public theorem b1_facts : ProOk 40 0 slots (after b1 (after b0 entryS)) = true ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b1 (after b0 entryS)).reg .r8 = some r8S ∧
    (after b1 (after b0 entryS)).reg .r9 = some (.load 2 0 8) ∧
    (after b1 (after b0 entryS)).reg .rax = some nS ∧
    (after b1 (after b0 entryS)).reg .rdi = some (.ptr 1 0) ∧
    (after b1 (after b0 entryS)).reg .rsi = some (.ptr 2 0) ∧
    (after b1 (after b0 entryS)).reg .rdx = some (.reg .rdx) ∧
    (after b1 (after b0 entryS)).reg .rcx = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).flags.zf =
      some (.cmp .eq .W64 (.bin .and .W64 nS nS) (.lit 0)) := by
  decide +kernel

/-- The registers the search keeps. -/
@[expose] public def keepS : List Reg64 := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9]

public theorem b2_facts : Quiet (after b2 regsS) ∧ Arrays.keepsRegs regsS (after b2 regsS) keepS ∧
    (after b2 regsS).reg .r10 = some (.bin .add .W64 (.reg .rdi) (.lit 8)) ∧
    (after b2 regsS).reg .r11 =
      some (.ite (.not (.cmp .ult .W64 (.reg .r9) (.lit 3))) (.lit 8)
        (.bin .add .W64 (.reg .rsi) (.lit 8))) ∧
    (after b2 regsS).reg .rbx = some (.ite (.cmp .ult .W64 (.reg .r9) (.lit 3)) (.reg .r9) (.lit 0)) ∧
    (after b2 regsS).reg .r14 = some (.lit 8) := by
  unfold Quiet; decide +kernel

/-- The registers the search loop keeps. -/
@[expose] public def keepL : List Reg64 := keepS ++ [.r11, .rbx, .r14]

public theorem b4_facts : Quiet (after b4 regsS) ∧ Arrays.keepsRegs regsS (after b4 regsS) keepL ∧
    (after b4 regsS).reg .r10 = some (.bin .add .W64 (.lit 40) (.reg .r10)) ∧
    (after b4 regsS).flags.zf = some (.cmp .eq .W64 (.bin .add .W64 (.lit 40) (.reg .r10)) (.reg .r8)) := by
  unfold Quiet; decide +kernel

public theorem b5_facts : Quiet (after b5 degS) ∧
    Arrays.keepsRegs degS (after b5 degS) (.r10 :: keepL) ∧
    (after b5 degS).flags.zf = some (.cmp .eq .W64 (.load 1 0 8) (.reg .r9)) := by
  unfold Quiet; decide +kernel

public theorem b6_facts : Quiet (after b6 regsS) ∧
    Arrays.keepsRegs regsS (after b6 regsS) (.r10 :: keepL) ∧
    (after b6 regsS).reg .r15 =
      some (.ite (.not (.cmp .ult .W64 (.reg .r9) (.lit 3))) (.reg .r14)
        (.bin .add .W64 (.reg .r10) (.lit 8))) ∧
    (after b6 regsS).reg .r12 = some (.lit 0) := by
  unfold Quiet; decide +kernel

public theorem b7_facts : Quiet (after b7 regsS) ∧
    Arrays.keepsRegs regsS (after b7 regsS) (.r10 :: .r12 :: .r15 :: keepL) ∧
    (after b7 regsS).flags.zf = some (.cmp .eq .W64 (.reg .rbx) (.reg .r12)) := by
  unfold Quiet; decide +kernel

public theorem b8_facts : Quiet (after b8 colS) ∧
    Arrays.keepsRegs colS (after b8 colS) (.r10 :: .r15 :: keepL) ∧
    (after b8 colS).reg .r12 = some (.bin .add .W64 (.reg .r12) (.lit 1)) ∧
    (after b8 colS).flags.zf = some (.cmp .eq .W64 (.loadx 1 8 (.bin .mul .W64 (.reg .r12) (.lit 8)) 8)
      (.loadx 2 8 (.bin .mul .W64 (.reg .r12) (.lit 8)) 8)) := by
  unfold Quiet; decide +kernel

public theorem b9_facts : Quiet (after b9 regsS) ∧
    Arrays.keepsRegs regsS (after b9 regsS) (.r10 :: keepL) := by
  unfold Quiet; decide +kernel

public theorem b11_facts : MidOk 40 0 slots (after b11 foundS) = true ∧
    (∀ w ∈ (after b11 foundS).mem, w.r = 1 ∧ 24 ≤ w.off ∧ w.off + w.n ≤ 40) ∧
    (∀ i < 8, findWrite 1 (24 + i) (after b11 foundS).mem =
      some (.bin .xor .W64 (.load 1 24 8) (.reg .rdx), i)) ∧
    (∀ i < 8, findWrite 1 (24 + 8 + i) (after b11 foundS).mem =
      some (.bin .xor .W64 (.load 1 32 8) (.reg .rcx), i)) := by
  decide +kernel

public theorem b12_facts : Quiet (after b12 regsS) ∧
    Arrays.keepsRegs regsS (after b12 regsS) keepL ∧
    (after b12 regsS).flags.zf = some (.cmp .eq .W64 (.reg .rax) (.lit 148)) := by
  unfold Quiet; decide +kernel

public theorem b13_facts : Quiet (after b13 regsS) ∧ (after b13 regsS).reg .rax = some (.lit 0) := by
  unfold Quiet; decide +kernel

public theorem b14_facts : MidOk 40 0 slots (after b14 pushS) = true ∧
    (∀ w ∈ (after b14 pushS).mem, (w.r = 1 ∧ w.off + w.n ≤ 40) ∨ (w.r = 3 ∧ w.off + w.n ≤ 8)) ∧
    (∀ i < 8, findWrite 3 (0 + i) (after b14 pushS).mem =
      some (.bin .add .W64 (.reg .rax) (.lit 1), i)) ∧
    (∀ i < 8, findWrite 1 (0 + i) (after b14 pushS).mem = some (.reg .r9, i)) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b14 pushS).mem = some (.load 2 8 8, i)) ∧
    (∀ i < 8, findWrite 1 (16 + i) (after b14 pushS).mem = some (.load 2 16 8, i)) ∧
    (∀ i < 8, findWrite 1 (24 + i) (after b14 pushS).mem = some (.reg .rdx, i)) ∧
    (∀ i < 8, findWrite 1 (24 + 8 + i) (after b14 pushS).mem = some (.reg .rcx, i)) := by
  decide +kernel

public theorem b15_facts : Quiet (after b15 regsS) ∧
    (after b15 regsS).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) := by
  unfold Quiet; decide +kernel

public theorem b16_facts : EpiOk 40 slots (after b16 regsS) = true ∧ (after b16 regsS).mem = [] ∧
    (after b16 regsS).reg .rax = some (.reg .rax) := by
  decide +kernel

end NativeRustcVmX64.Layout.FormBufAddTerm
