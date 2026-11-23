module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.FoldRow
public meta import NativeRustcVmX64.Code.Vm.FoldRow
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `fold_row`'s blocks, run by the symbolic executor (x86-64)

Region 0 of the frame's environment is the 96-byte frame (`Field.frameS 96`, `Field.midS 96`:
the pushes from offset 48, the 40 bytes of locals, the calls' return-address slot at 0) and the
return address. From RSP (offset `8`): the factor's limbs `c1` at offset 8, `c0` at 16, the rounds'
end at 24, `x` at 32, the round's pointer at 40.
- `b0a` (`entryS`): the prologue; `b0b`, `b1`, `b3` (`midS`): `x` spilled, the rounds' end, the
  next round;
- `b4` (`rdS`: the frame, region 1 the round RCX points to): `α`, `β` loaded, `kmul(x, β.c0)`;
  `b5`, `b6`, `b7` (`midS`): `kmul(x, β.c1)`, the size halved, the factor `α + β·x`;
- `b9`, `b10`, `b13` (`regsS`): the turn's counters, the result's test;
- `b11` (`pairS`: the frame, region 1 lanes `2i`, `2i + 1` at `r14 + 2·r13 − 16`): `EW::mul`;
- `b12` (`laneS`: region 0 lane `i` at `r14 + r13 − 8`): the lane stored;
- `b14` (`firstS`: region 0 lane `0`): the result; `b15` (`midS`): the epilogue.
-/

namespace NativeRustcVmX64.Whir.FoldRow

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.FoldRow NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs keepsAll freeRegs restores)

@[expose] public section

/-- `r14 + 2·r13`: lane `2i + 1`'s address in `b11`. -/
def pairAddr : Sym := .bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .r13) (.lit 2))
/-- `r14 + r13`: lane `i`'s address plus 8 in `b12`. -/
def laneAddr : Sym := .bin .add .W64 (.reg .r14) (.reg .r13)

/-- At the entry. -/
abbrev entryS : SState := frameS 96
/-- Registers only. -/
def regsS : SState := init []
/-- At `b4`: the frame, the round. -/
def rdS : SState := init [104, 32] [(.rsp, .ptr 0 8), (.rcx, .ptr 1 0)]
/-- At `b11`: the frame, the two lanes. -/
def pairS : SState := init [104, 32] [(.rsp, .ptr 0 8)] [] [] [(pairAddr, 1, 16)]
/-- At `b12`: lane `i`. -/
def laneS : SState := init [16] [] [] [] [(laneAddr, 0, 8)]
/-- At `b14`: lane `0`. -/
def firstS : SState := init [16] [(.r14, .ptr 0 0)]

/-- The prologue. -/
def b0a : List Directive := b0.take 8
/-- `x` spilled, the rounds' count tested. -/
def b0b : List Directive := b0.drop 8

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(88, .rbp), (80, .r15), (72, .r14), (64, .r13), (56, .r12), (48, .rbx)]

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (midS 96)
sym_block run_b1 := exec b1 (midS 96)
sym_block run_b3 := exec b3 (midS 96)
sym_block run_b4 := exec b4 rdS
sym_block run_b5 := exec b5 (midS 96)
sym_block run_b6 := exec b6 (midS 96)
sym_block run_b7 := exec b7 (midS 96)
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 regsS
sym_block run_b11 := exec b11 pairS
sym_block run_b12 := exec b12 laneS
sym_block run_b13 := exec b13 regsS
sym_block run_b14 := exec b14 firstS
sym_block run_b15 := exec b15 (midS 96)

public theorem b0a_entry : (∀ p ∈ slots, p.1 + 8 ≤ 96 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0a entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧
    (after b0a entryS).reg .rsp = some (.ptr 0 8) ∧
    (∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], (after b0a entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b0b_write : keepsRegs (midS 96) (after b0b (midS 96)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b0b (midS 96)).mem, w.r = 0 ∧ 32 ≤ w.off ∧ w.off + w.n ≤ 40) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b0b (midS 96)).mem = some (.reg .rdx, i)) := by
  decide +kernel

public theorem b1_write : keepsRegs (midS 96) (after b1 (midS 96)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b1 (midS 96)).mem, w.r = 0 ∧ 24 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b1 (midS 96)).mem =
      some (.bin .add .W64 (.reg .rcx) (.bin .shl .W64 (.reg .r8) (.lit 5)), i)) := by
  decide +kernel

public theorem b3_keeps : keepsAll (midS 96) (after b3 (midS 96)) (freeRegs slots) = true := by
  decide +kernel

public theorem b4_call : keepsRegs rdS (after b4 rdS) (freeRegs slots) = true ∧
    (after b4 rdS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b4 rdS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off) ∧ w.off + w.n ≤ 48) ∧
    (∀ i < 8, findWrite 0 (40 + i) (after b4 rdS).mem = some (.ptr 1 0, i)) := by
  decide +kernel

public theorem b5_call : keepsRegs (midS 96) (after b5 (midS 96)) (freeRegs slots) = true ∧
    (after b5 (midS 96)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b5 (midS 96)).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 16 ≤ w.off) ∧
      w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b5 (midS 96)).mem = some (.reg .rax, i)) := by
  decide +kernel

public theorem b6_write : keepsRegs (midS 96) (after b6 (midS 96)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b6 (midS 96)).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b6 (midS 96)).mem = some (.reg .rax, i)) := by
  decide +kernel

public theorem b7_write : keepsRegs (midS 96) (after b7 (midS 96)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b7 (midS 96)).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b7 (midS 96)).mem =
      some (.bin .xor .W64 (.load 0 8 8) (.reg .r12), i)) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b7 (midS 96)).mem =
      some (.bin .xor .W64 (.load 0 16 8) (.reg .r13), i)) := by
  decide +kernel

public theorem b9_keeps : keepsAll regsS (after b9 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b10_keeps : keepsAll regsS (after b10 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b13_keeps : keepsAll regsS (after b13 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b14_keeps : keepsAll firstS (after b14 firstS) (freeRegs slots) = true := by
  decide +kernel

public theorem b11_call : keepsRegs pairS (after b11 pairS) (freeRegs slots) = true ∧
    (after b11 pairS).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b11 pairS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b12_write : keepsRegs laneS (after b12 laneS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b12 laneS).mem, w.r = 0 ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b12 laneS).mem =
      some (.bin .xor .W64 (.reg .rax) (.reg .rbp), i)) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b12 laneS).mem =
      some (.bin .xor .W64 (.reg .rdx) (.reg .r15), i)) := by
  decide +kernel

public theorem b15_restores : restores slots 96 (after b15 (midS 96)) = true ∧
    (after b15 (midS 96)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 48 ≤ p.1 ∧ p.1 + 8 ≤ 96 := by decide

end NativeRustcVmX64.Whir.FoldRow
