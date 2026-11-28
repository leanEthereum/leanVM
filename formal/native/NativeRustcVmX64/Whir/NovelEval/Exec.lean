module

public import NativeRustcVmX64.Whir.MathFrame
public import NativeRustcVmX64.Code.Vm.NovelEval
public meta import NativeRustcVmX64.Code.Vm.NovelEval
public meta import NativeRustcVmX64.Whir.MathFrame

/-!
# `novel_eval`'s blocks, run by the symbolic executor (x86-64)

Region 0 of the frame's environment is the 1104-byte frame (`Field.frameS 1104`,
`Field.midS 1104`: the pushes from offset 1056, the 1048 bytes of locals, the calls'
return-address slot at 0) and the return address. From RSP (offset `8`): the end of the `What`s
(later the products' byte count) at offset 8, the output pointer at 16, the coefficients' pointer
at 24, the basis (128 words) from 32.
- `b0a` (`entryS`): the prologue; `b0b` (`midS`): the arguments, `memset` of the basis but its
  first word;
- `b1` (`regsS`), `b2`, `b3`, `b4` (`midS`): the count's test, the spills, the doubling loop's
  head;
- `b5` (`w5S`: region 0 the `What` R12 points to): the inner loop's registers;
- `b6a` (`ldS`: region 0 the basis word R14 points to), `b6b` (`midS`): `kmul`;
- `b7` (`hiS`: region 0 the basis word at `r14 + 8·rbp`): the product stored;
- `b8`, `b9` (`regsS`), `b10` (`midS`): the doubling's end, the sum's count;
- `b11a` (`sumS`: region 0 the frame's first 32 bytes, region 1 the basis word at
  `24 + rsp + r15`, region 2 the coefficient at `coefficients + 2·r15`), `b11b`, `b12`, `b13`
  (`midS`): the sum's turn, two `kmul`s;
- `b14`, `b15` (`regsS`); `b16` (`outS`: the frame, region 1 the output): `Some`'s value;
  `b17a` (`tagS`: region 0 the output's tag R15 points to), `b17b` (`midS`): the epilogue.
-/

namespace NativeRustcVmX64.Whir.NovelEval

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.NovelEval NativeRustcVmX64.Field
open NativeRustcVmX64.Arrays (keepsRegs keepsAll freeRegs restores)

@[expose] public section

/-- The high basis word's address in `b7`: `r14 + 8·rbp`. -/
def hiAddr : Sym := .bin .add .W64 (.reg .r14) (.bin .mul .W64 (.reg .rbp) (.lit 8))
/-- The basis word's address in `b11a`. -/
def bAddr : Sym := .bin .add .W64 (.bin .add .W64 (.ptr 0 8) (.reg .r15)) (.lit 24)
/-- The coefficient's address in `b11a`. -/
def cAddr : Sym := .bin .add .W64 (.load 0 24 8) (.bin .mul .W64 (.reg .r15) (.lit 2))

/-- At the entry. -/
abbrev entryS : SState := frameS 1104
/-- Registers only. -/
def regsS : SState := init []
/-- At `b5`: the `What` R12 points to. -/
def w5S : SState := init [8] [(.r12, .ptr 0 0)]
/-- At `b6a`: the basis word R14 points to. -/
def ldS : SState := init [8] [(.r14, .ptr 0 0)]
/-- At `b7`: the high basis word. -/
def hiS : SState := init [8] [] [] [] [(hiAddr, 0, 0)]
/-- At `b11a`: the frame's first 32 bytes, the basis word, the coefficient. -/
def sumS : SState := init [32, 8, 16] [(.rsp, .ptr 0 8)] [] [] [(bAddr, 1, 0), (cAddr, 2, 0)]
/-- At `b16`: the frame, the output the spilled pointer points to. -/
def outS : SState := init [1112, 24] [(.rsp, .ptr 0 8)] [] [] [(.load 0 16 8, 1, 0)]
/-- At `b17a`: the output's tag R15 points to. -/
def tagS : SState := init [8] [(.r15, .ptr 0 0)]

/-- The prologue. -/
def b0a : List Directive := b0.take 8
/-- The arguments and `memset`. -/
def b0b : List Directive := b0.drop 8
/-- The basis word's load. -/
def b6a : List Directive := b6.take 3
/-- `kmul`. -/
def b6b : List Directive := b6.drop 3
/-- The sum's loads. -/
def b11a : List Directive := b11.take 6
/-- `kmul`. -/
def b11b : List Directive := b11.drop 6
/-- The tag's store. -/
def b17a : List Directive := b17.take 2
/-- The epilogue. -/
def b17b : List Directive := b17.drop 2

/-- The pushed registers' slots. -/
def slots : List (Nat × Reg64) :=
  [(1096, .rbp), (1088, .r15), (1080, .r14), (1072, .r13), (1064, .r12), (1056, .rbx)]

end

set_option Elab.async false

sym_block run_b0a := exec b0a entryS
sym_block run_b0b := exec b0b (gotMidS 1104 "memset")
sym_block run_b1 := exec b1 regsS
sym_block run_b2 := exec b2 (midS 1104)
sym_block run_b3 := exec b3 (midS 1104)
sym_block run_b4 := exec b4 (midS 1104)
sym_block run_b5 := exec b5 w5S
sym_block run_b6a := exec b6a ldS
sym_block run_b6b := exec b6b (midS 1104)
sym_block run_b7 := exec b7 hiS
sym_block run_b8 := exec b8 regsS
sym_block run_b9 := exec b9 regsS
sym_block run_b10 := exec b10 (midS 1104)
sym_block run_b11a := exec b11a sumS
sym_block run_b11b := exec b11b (midS 1104)
sym_block run_b12 := exec b12 (midS 1104)
sym_block run_b13 := exec b13 (midS 1104)
sym_block run_b14 := exec b14 regsS
sym_block run_b15 := exec b15 regsS
sym_block run_b16 := exec b16 outS
sym_block run_b17a := exec b17a tagS
sym_block run_b17b := exec b17b (midS 1104)

public theorem b0a_entry : (∀ p ∈ slots, p.1 + 8 ≤ 1104 ∧
      ∀ i < 8, findWrite 0 (p.1 + i) (after b0a entryS).mem = some (.reg p.2, i)) ∧
    (∀ r ∈ freeRegs slots, (after b0a entryS).reg r = some (.reg r)) ∧
    (∀ w ∈ (after b0a entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1104) ∧
    (after b0a entryS).reg .rsp = some (.ptr 0 8) ∧
    (∀ r ∈ [Reg64.rdi, .rsi, .rdx, .rcx, .r8], (after b0a entryS).reg r = some (.reg r)) := by
  decide +kernel

public theorem b0b_call : keepsRegs (gotMidS 1104 "memset") (after b0b (gotMidS 1104 "memset")) (freeRegs slots) = true ∧
    (after b0b (gotMidS 1104 "memset")).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b0b (gotMidS 1104 "memset")).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b1_keeps : keepsAll regsS (after b1 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b2_write : keepsRegs (midS 1104) (after b2 (midS 1104)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b2 (midS 1104)).mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 40) ∧
    (∀ i < 8, findWrite 0 (32 + i) (after b2 (midS 1104)).mem = some (.lit 1, i)) ∧
    (∀ i < 8, findWrite 0 (16 + i) (after b2 (midS 1104)).mem = some (.reg .r15, i)) ∧
    (∀ i < 8, findWrite 0 (24 + i) (after b2 (midS 1104)).mem = some (.reg .rbp, i)) := by
  decide +kernel

public theorem b3_write : keepsRegs (midS 1104) (after b3 (midS 1104)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b3 (midS 1104)).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b3 (midS 1104)).mem =
      some (.bin .add .W64 (.reg .r12) (.bin .mul .W64 (.reg .r13) (.lit 8)), i)) := by
  decide +kernel

public theorem b4_keeps : keepsAll (midS 1104) (after b4 (midS 1104)) (freeRegs slots) = true := by
  decide +kernel
public theorem b5_keeps : keepsAll w5S (after b5 w5S) (freeRegs slots) = true := by
  decide +kernel
public theorem b6a_keeps : keepsAll ldS (after b6a ldS) (freeRegs slots) = true := by
  decide +kernel

public theorem b6b_call : keepsRegs (midS 1104) (after b6b (midS 1104)) (freeRegs slots) = true ∧
    (after b6b (midS 1104)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b6b (midS 1104)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b7_write : keepsRegs hiS (after b7 hiS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b7 hiS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b7 hiS).mem = some (.reg .rax, i)) := by
  decide +kernel

public theorem b8_keeps : keepsAll regsS (after b8 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b9_keeps : keepsAll regsS (after b9 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b10_write : keepsRegs (midS 1104) (after b10 (midS 1104)) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b10 (midS 1104)).mem, w.r = 0 ∧ 8 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (∀ i < 8, findWrite 0 (8 + i) (after b10 (midS 1104)).mem =
      some (.bin .shl .W64 (.reg .r14) (.lit 3), i)) := by
  decide +kernel

public theorem b11a_keeps : keepsAll sumS (after b11a sumS) (freeRegs slots) = true := by
  decide +kernel

public theorem b11b_call : keepsRegs (midS 1104) (after b11b (midS 1104)) (freeRegs slots) = true ∧
    (after b11b (midS 1104)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b11b (midS 1104)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b12_call : keepsRegs (midS 1104) (after b12 (midS 1104)) (freeRegs slots) = true ∧
    (after b12 (midS 1104)).reg .rsp = some (.ptr 0 0) ∧
    (∀ w ∈ (after b12 (midS 1104)).mem, w.r = 0 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem b13_keeps : keepsAll (midS 1104) (after b13 (midS 1104)) (freeRegs slots) = true := by
  decide +kernel
public theorem b14_keeps : keepsAll regsS (after b14 regsS) (freeRegs slots) = true := by
  decide +kernel
public theorem b15_keeps : keepsAll regsS (after b15 regsS) (freeRegs slots) = true := by
  decide +kernel

public theorem b16_write : keepsRegs outS (after b16 outS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b16 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    (∀ i < 8, findWrite 1 (8 + i) (after b16 outS).mem = some (.reg .r14, i)) ∧
    (∀ i < 8, findWrite 1 (8 + 8 + i) (after b16 outS).mem = some (.reg .rbx, i)) := by
  decide +kernel

public theorem b17a_write : keepsRegs tagS (after b17a tagS) (.rsp :: freeRegs slots) = true ∧
    (∀ w ∈ (after b17a tagS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (∀ i < 8, findWrite 0 (0 + i) (after b17a tagS).mem = some (.reg .rbx, i)) := by
  decide +kernel

public theorem b17b_restores : restores slots 1104 (after b17b (midS 1104)) = true ∧
    (after b17b (midS 1104)).mem = [] := by
  decide +kernel

public theorem slots_ok : ∀ p ∈ slots, 1056 ≤ p.1 ∧ p.1 + 8 ≤ 1104 := by decide

public theorem freeRegs_nil : freeRegs slots = [] := by decide

end NativeRustcVmX64.Whir.NovelEval
