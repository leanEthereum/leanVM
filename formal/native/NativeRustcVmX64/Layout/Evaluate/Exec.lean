module

public import NativeRustcVmX64.Layout.Common
public import NativeRustcVmX64.Code.Vm.Evaluate
public meta import NativeRustcVmX64.Code.Vm.Evaluate
public meta import NativeRustcVmX64.Layout.Common

/-!
# `evaluate`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the frame (`Field.frameS 96`, `Field.midS 96`): the six pushes (offsets `48`-`96`),
the locals (the terms' address at `16`, their count at `24`, the sum at `32`, `40`), the call's
return-address slot at `0`, the return address above.
- `entryS` at the entry: `b0` the prologue, then `b1` (the loop's set-up) or `b12` (no terms);
- `termS` at the outer loop's head `.L3` (`b4`): the frame, term `i` (region 1, at `termAddr`);
- `colS` at a column's load `.L5` (`b10`): column `j` (region 0, at `colAddr`);
- `elemS` at a row element's load `.L7` (`b7`): the element (region 0, at `elemAddr`);
- `regsS`: blocks that touch no memory (`b5`, `b9`, `b11`, `b12`);
- `Field.midS 96` at the call `.L8` (`b8`), the term's end `.L9` (`b3`) and the epilogue (`b13`).
-/

namespace NativeRustcVmX64.Layout.Evaluate

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Evaluate NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (after freeRegs keepsAll keepsRegs restores)

@[expose] public section

/-- At the entry. -/
abbrev entryS : SState := frameS 96

/-- `5 i`, as `leaq (%r12,%r12,4)` computes it. -/
def fiveI : Sym := .bin .add .W64 (.reg .r12) (.bin .mul .W64 (.reg .r12) (.lit 4))

/-- Term `i`'s address: the terms' (the frame's word `16`) plus `8 · 5 i`. -/
def termAddr : Sym := .bin .add .W64 (.load 0 16 8) (.bin .mul .W64 fiveI (.lit 8))

/-- At `.L3`: the frame, term `i` (region 1). -/
def termS : SState := init [104, 40] [(.rsp, .ptr 0 8)] [] [] [(termAddr, 1, 0)]

/-- Column `j`'s address: RBX plus `8 j`. -/
def colAddr : Sym := .bin .add .W64 (.reg .rbx) (.bin .mul .W64 (.reg .rbp) (.lit 8))

/-- At `.L5`: column `j` (region 0). -/
def colS : SState := init [8] [] [] [] [(colAddr, 0, 0)]

/-- The row element's address: R15 plus `16 c`. -/
def elemAddr : Sym := .bin .add .W64 (.reg .r15) (.bin .shl .W64 (.reg .rcx) (.lit 4))

/-- At `.L7`: the row's element (region 0). -/
def elemS : SState := init [16] [] [] [] [(elemAddr, 0, 0)]

/-- Registers only. -/
def regsS : SState := init []

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(88, .rbp), (80, .r15), (72, .r14), (64, .r13), (56, .r12), (48, .rbx)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b12 := exec b12 (after b0 entryS)
sym_block run_b4 := exec b4 termS
sym_block run_b5 := exec b5 regsS
sym_block run_b10 := exec b10 colS
sym_block run_b7 := exec b7 elemS
sym_block run_b11 := exec b11 regsS
sym_block run_b8 := exec b8 (midS 96)
sym_block run_b9 := exec b9 regsS
sym_block run_b3 := exec b3 (midS 96)
sym_block run_b13 := exec b13 (midS 96)

/-- The prologue's facts, at the end of `b1` or `b12` (`S` the state there). -/
@[expose] public def EntryOk (S : SState) : Prop :=
  (∀ p ∈ slots, p.1 + 8 ≤ 96 ∧ ∀ i < 8, findWrite 0 (p.1 + i) S.mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, S.reg r = some (.reg r)) ∧
    (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧ S.reg .rsp = some (.ptr 0 8) ∧
    (∀ i < 8, findWrite 0 (16 + i) S.mem = some (.reg .rdi, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) S.mem = some (.reg .rsi, i)) ∧
    S.reg .rax = some (.lit 0) ∧ S.reg .rdx = some (.lit 0)

public theorem b0_cond : (after b0 entryS).flags.zf =
    some (.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)) := by
  decide +kernel

public theorem b1_entry : EntryOk (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.lit 0) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .r15 = some (.reg .rdx) := by
  unfold EntryOk; decide +kernel

public theorem b12_entry : EntryOk (after b12 (after b0 entryS)) := by
  unfold EntryOk; decide +kernel

/-- `b4`'s branch: past the degree's `3`-offset, below `2 ^ 64 - 2`. -/
@[expose] public def degCond : SBool := .cmp .ult .W64 (.bin .sub .W64 (.load 1 0 8) (.lit 3)) (.lit 18446744073709551614)

/-- `b4`'s columns' address: `termAddr + 8`, or `8` past a degree of `3`. -/
@[expose] public def rbxS : Sym := .ite (.not (.cmp .ult .W64 (.load 1 0 8) (.lit 3))) (.lit 8) (.bin .add .W64 termAddr (.lit 8))

public theorem b4_facts : keepsRegs termS (after b4 termS) (.rsp :: freeRegs slots) = true ∧
    keepsRegs termS (after b4 termS) [.r12, .r14, .r15] = true ∧
    (∀ w ∈ (after b4 termS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ w ∈ (after b4 termS).mem, w.r = 0 ∧ (w.off + w.n ≤ 16 ∨ 32 ≤ w.off)) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b4 termS).mem = some (.reg .rax, i)) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b4 termS).mem = some (.reg .rdx, i)) ∧
    (after b4 termS).reg .rax = some (.load 1 24 8) ∧
    (after b4 termS).reg .rdx = some (.load 1 (24 + 8) 8) ∧
    (after b4 termS).reg .r13 = some (.load 1 0 8) ∧ (after b4 termS).reg .rbx = some rbxS ∧
    (after b4 termS).flags.cf = some degCond := by
  decide +kernel

/-- The registers the inner loop keeps. -/
@[expose] public def keepI : List Reg64 := [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15]

public theorem b5_facts : keepsAll regsS (after b5 regsS) (freeRegs slots) = true ∧
    keepsRegs regsS (after b5 regsS) [.rax, .rdx, .rbx, .r12, .r13, .r14, .r15] = true ∧
    (after b5 regsS).reg .rbp = some (.lit 0) := by
  decide +kernel

public theorem b10_facts : keepsAll colS (after b10 colS) (freeRegs slots) = true ∧
    keepsRegs colS (after b10 colS) keepI = true ∧
    (after b10 colS).reg .rcx = some (.load 0 0 8) ∧
    (after b10 colS).flags.cf = some (.cmp .ult .W64 (.load 0 0 8) (.reg .r14)) := by
  decide +kernel

public theorem b7_facts : keepsAll elemS (after b7 elemS) (freeRegs slots) = true ∧
    keepsRegs elemS (after b7 elemS) keepI = true ∧
    (after b7 elemS).reg .r8 = some (.load 0 0 8) ∧
    (after b7 elemS).reg .rcx = some (.load 0 (0 + 8) 8) := by
  decide +kernel

public theorem b11_facts : keepsAll regsS (after b11 regsS) (freeRegs slots) = true ∧
    keepsRegs regsS (after b11 regsS) keepI = true ∧
    (after b11 regsS).reg .r8 = some (.lit 0) ∧ (after b11 regsS).reg .rcx = some (.lit 0) := by
  decide +kernel

public theorem b8_call : keepsRegs (midS 96) (after b8 (midS 96)) (freeRegs slots) = true ∧
    keepsRegs (midS 96) (after b8 (midS 96)) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true ∧
    (after b8 (midS 96)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b8 (midS 96)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b8 (midS 96)).reg .rdi = some (.reg .rax) ∧
    (after b8 (midS 96)).reg .rsi = some (.reg .rdx) ∧
    (after b8 (midS 96)).reg .rdx = some (.reg .r8) ∧
    (after b8 (midS 96)).reg .rcx = some (.reg .rcx) := by
  decide +kernel

public theorem b9_facts : keepsAll regsS (after b9 regsS) (freeRegs slots) = true ∧
    keepsRegs regsS (after b9 regsS) [.rax, .rdx, .rbx, .r12, .r13, .r14, .r15] = true ∧
    (after b9 regsS).reg .rbp = some (.bin .add .W64 (.reg .rbp) (.lit 1)) ∧
    (after b9 regsS).flags.zf =
      some (.cmp .eq .W64 (.reg .r13) (.bin .add .W64 (.reg .rbp) (.lit 1))) := by
  decide +kernel

public theorem b3_facts : keepsAll (midS 96) (after b3 (midS 96)) (freeRegs slots) = true ∧
    keepsRegs (midS 96) (after b3 (midS 96)) [.r14, .r15] = true ∧
    (after b3 (midS 96)).reg .rax = some (.bin .xor .W64 (.load 0 32 8) (.reg .rax)) ∧
    (after b3 (midS 96)).reg .rdx = some (.bin .xor .W64 (.load 0 40 8) (.reg .rdx)) ∧
    (after b3 (midS 96)).reg .r12 = some (.bin .add .W64 (.reg .r12) (.lit 1)) ∧
    (after b3 (midS 96)).flags.zf =
      some (.cmp .eq .W64 (.bin .add .W64 (.reg .r12) (.lit 1)) (.load 0 24 8)) := by
  decide +kernel

public theorem b13_restores : restores slots 96 (after b13 (midS 96)) = true ∧
    (after b13 (midS 96)).mem = [] ∧ (after b13 (midS 96)).reg .rax = some (.reg .rax) ∧
    (after b13 (midS 96)).reg .rdx = some (.reg .rdx) := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 48 ≤ p.1 ∧ p.1 + 8 ≤ 96 := by decide

end NativeRustcVmX64.Layout.Evaluate
