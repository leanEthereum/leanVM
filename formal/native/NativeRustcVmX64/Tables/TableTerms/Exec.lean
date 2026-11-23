module

public import NativeRustcVmX64.Tables.TableTerms.Body
public import NativeRustcVmX64.Code.Vm.TableTerms
public import NativeRustcVmX64.Code.Vm.BufEW30Extend.Names
public import NativeRustcVmX64.Code.Vm.ConstraintsW.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.Evaluate.Names
public import NativeRustcVmX64.Code.Vm.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public import NativeRustcVmX64.Code.Vm.TableTerms.Names
public meta import NativeRustcVmX64.Code.Vm.TableTerms

/-!
# `table_terms`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 272-byte frame below the entry's RSP and the return address (`Frame`, `F = 272`:
RSP at offset `8` in the body, a callee's return address at `0`): `out` at `8`, table `i`'s
evaluations' entry at `16`, the constraint powers at `24`, the form powers at `32`, the point at
`40`, `48`, the `TState` at `56`, the weight at `64`, `72`, the constraints' dot at `80`, `88`,
the constraint count at `96`, the cursor at `104`, the `TABLES` walk (`16 + 40 i`) at `112`, the
running sum at `120`, `128`, the heights' walk (`8 i`) at `136`, the constraints at `144` (32
bytes), the three form values at `176` (48 bytes), the pushed registers from `224`. Region 1 is
the four stack arguments (heights, forms, weights, evaluations) above the return address, at the
frame's offsets `280` to `312` (aliases).

- `entryS` (`b0`): the frame, the arguments.
- `tabS` (`b1`, `b4`): region 1 table `i`'s 40-byte `TABLES` entry, R14 + RBP its byte `16`.
- `evS` (`b2`): region 1 table `i`'s evaluations' entry (1968 bytes), the word at `16`.
- `formS` (`b6` to `b8`): region 1 table `i`'s three forms (17784 bytes), R13 their byte `11864`.
- `wS` (`b9`): region 1 the arguments, region 2 the table's weight (16 bytes) at the weights plus
  twice the word at `136`.
- `ptS` (`b10`): region 1 the arguments, region 2 the entry's first word (the word at `16`), region
  3 the table's height (the heights plus R12).
- `outS` (`b14`, `b15`): region 1 `out` (24 bytes), the word at `8`.
- `sF` (`b3`, `b5`, `b11` to `b13`, `b16`): the frame only.
-/

namespace NativeRustcVmX64.Tables.TableTerms

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TableTerms
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Tables.Body

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(264, .rbp), (256, .r15), (248, .r14), (240, .r13), (232, .r12), (224, .rbx)]

/-- `TABLES`' label. -/
abbrev tablesL : Label := NativeRustcVmX64.Vm.Symbols.rodata4Label

/-- `test %al, %al`, zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- `b1`'s exit: the width at least `93`. -/
def c1 : SBool := .not (.cmp .ult .W64 (.load 1 8 8) (.lit 93))

/-- `b13`'s exit: not the sixth table. -/
def c13 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 40) (.reg .rbp)) (.lit 256))

/-- `2 - cursor`, saturating. -/
def sub2 : Sym := .ite (.cmp .ult .W64 (.lit 2) (.reg .r15)) (.lit 0) (.bin .sub .W64 (.lit 2) (.reg .r15))

/-- `b5`'s constraint powers from the cursor. -/
def rdi5 : Sym := .ite (.not (.cmp .ult .W64 (.reg .r15) (.lit 3))) (.lit 8)
  (.bin .add .W64 (.load 0 24 8) (.bin .shl .W64 (.reg .r15) (.lit 4)))

/-- `b5`'s count: the table's constraints, at most `2 - cursor`. -/
def rsi5 : Sym := .ite (.cmp .ult .W64 (.reg .r14) sub2) (.reg .r14) sub2

/-- A form's length at least `149`. -/
def cF (o : Nat) : SBool := .not (.cmp .ult .W64 (.load 1 o 8) (.lit 149))

/-- `b10`'s count: the height, at most the point's length. -/
def rdx10 : Sym := .ite (.not (.cmp .ult .W64 (.load 3 0 8) (.load 0 48 8))) (.load 0 48 8) (.load 3 0 8)

/-- R14 + RBP in the loop: byte `16` of table `i`'s `TABLES` entry. -/
def tabA : Sym := .bin .add .W64 (.reg .r14) (.reg .rbp)

/-- The weight's address in `b9`: the weights plus twice the heights' walk. -/
def wAS : Sym := .bin .add .W64 (.load 1 16 8) (.bin .mul .W64 (.load 0 136 8) (.lit 2))

/-- The height's address in `b10`: the heights plus R12. -/
def hAS : Sym := .bin .add .W64 (.load 1 0 8) (.reg .r12)

def entryS : SState :=
  init [280, 32] [(.rsp, .ptr 0 272)] [] [] [(.ptr 0 288, 1, 8), (.ptr 0 304, 1, 24)]
def tabS : SState := init [280, 40] [(.rsp, .ptr 0 8)] [] [] [(tabA, 1, 16)]
def evS : SState := init [280, 1968] [(.rsp, .ptr 0 8)] [] [] [(.load 0 16 8, 1, 0)]
def formS : SState := init [280, 17784] [(.rsp, .ptr 0 8)] [] [] [(.reg .r13, 1, 11864)]
def wS : SState := init [280, 32, 16] [(.rsp, .ptr 0 8)] [] [] [(.ptr 0 296, 1, 16), (wAS, 2, 0)]
def ptS : SState := init [280, 32, 8, 8] [(.rsp, .ptr 0 8)] [] []
  [(.ptr 0 280, 1, 0), (.load 0 16 8, 2, 0), (hAS, 3, 0)]
def outS : SState := init [280, 24] [(.rsp, .ptr 0 8)] [] [] [(.load 0 8 8, 1, 0)]
def sF : SState := init [280] [(.rsp, .ptr 0 8)]

/-- The frame's words the body keeps. -/
def U : List Nat := [8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 88, 96, 104, 112, 120, 128, 136, 144,
  152, 160, 168, 176, 184, 192, 200]

/-- The frame's words but `ex`. -/
def UW (ex : List Nat) : List Nat := U.filter fun o ↦ !ex.contains o

/-- A block's writes miss the frame's words at `os` (region `0`). -/
def missO (Sy : SState) (os : List Nat) : Bool :=
  os.all fun o ↦ Sy.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ o) || decide (o + 8 ≤ w.off)

/-- A block's writes in region `0` miss the bytes `lo` to `hi`. -/
def missR (Sy : SState) (lo hi : Nat) : Bool :=
  Sy.mem.all fun w ↦ w.r != 0 || decide (w.off + w.n ≤ lo) || decide (hi ≤ w.off)

/-- The callee-saved registers. -/
abbrev csR : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tabS
sym_block run_b2 := exec b2 evS
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 tabS
sym_block run_b5 := exec b5 sF
sym_block run_b6 := exec b6 formS
sym_block run_b7 := exec b7 formS
sym_block run_b8 := exec b8 formS
sym_block run_b9 := exec b9 wS
sym_block run_b10 := exec b10 ptS
sym_block run_b11 := exec b11 sF
sym_block run_b12 := exec b12 sF
sym_block run_b13 := exec b13 sF
sym_block run_b14 := exec b14 outS
sym_block run_b15 := exec b15 outS
sym_block run_b16 := exec b16 sF


section
open NativeRustcVmX64.Transcript (after after_eq)

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .fall) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 272 8 slots (after b0 entryS) = true ∧
    WrOk (after b0 entryS) [] = true ∧
    WordW 0 8 (.reg .rdi) (after b0 entryS) ∧ WordW 0 16 (.load 1 24 8) (after b0 entryS) ∧
    WordW 0 24 (.reg .rdx) (after b0 entryS) ∧ WordW 0 32 (.reg .rcx) (after b0 entryS) ∧
    WordW 0 40 (.reg .r8) (after b0 entryS) ∧ WordW 0 48 (.reg .r9) (after b0 entryS) ∧
    WordW 0 56 (.reg .rsi) (after b0 entryS) ∧
    (after b0 entryS).reg .r13 = some (.bin .add .W64 (.load 1 8 8) (.lit 11864)) ∧
    (after b0 entryS).reg .r14 = some (.lit 16) ∧
    (after b0 entryS).reg .rbp = some (.label tablesL) ∧
    (after b0 entryS).reg .rax = some (.lit 0) ∧ (after b0 entryS).reg .rcx = some (.lit 0) ∧
    (after b0 entryS).reg .rdx = some (.lit 0) ∧ (after b0 entryS).reg .r15 = some (.lit 0) := by
  decide +kernel

public theorem exit_b1 : exec b1 tabS = some (after b1 tabS, .cond c1 NativeRustcVmX64.Vm.TableTerms.label_6) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem ok_b1 : MidOk 272 8 slots (after b1 tabS) = true ∧ (after b1 tabS).mem = [] ∧
    (after b1 tabS).reg .r12 = some (.load 1 8 8) ∧
    Keeps (after b1 tabS) [.rax, .rcx, .rdx, .rbx, .rbp, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 evS = some (after b2 evS,
    .call NativeRustcVmX64.Vm.TStateReadScalars.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : missO (after b2 evS) (UW [120, 128, 136]) = true ∧
    MidOk 272 0 slots (after b2 evS) = true ∧ WrOk (after b2 evS) [1] = true ∧
    (∀ w ∈ (after b2 evS).mem, (w.r = 0 ∧ w.off + w.n ≤ 144) ∨ (w.r = 1 ∧ w.off = 488 ∧ w.n = 8)) ∧
    WordW 0 136 (.reg .rax) (after b2 evS) ∧ WordW 0 128 (.reg .rcx) (after b2 evS) ∧
    WordW 0 120 (.reg .rdx) (after b2 evS) ∧ WordW 1 488 (.reg .r12) (after b2 evS) ∧
    (after b2 evS).reg .rdi = some (.load 0 56 8) ∧
    (after b2 evS).reg .rsi = some (.bin .add .W64 (.load 0 16 8) (.lit 496)) ∧
    (after b2 evS).reg .rbx = some (.bin .add .W64 (.load 0 16 8) (.lit 496)) ∧
    (after b2 evS).reg .rdx = some (.reg .r12) ∧
    Keeps (after b2 evS) [.rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b3 : exec b3 sF = some (after b3 sF, .cond cAl NativeRustcVmX64.Vm.TableTerms.label_6) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem ok_b3 : MidOk 272 8 slots (after b3 sF) = true ∧ (after b3 sF).mem = [] ∧
    Keeps (after b3 sF) csR = true := by
  decide +kernel

public theorem exit_b4 : exec b4 tabS = some (after b4 tabS,
    .call NativeRustcVmX64.Vm.ConstraintsW.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : missO (after b4 tabS) (UW [112, 144, 152, 160, 168]) = true ∧
    MidOk 272 0 slots (after b4 tabS) = true ∧ WrOk (after b4 tabS) [] = true ∧
    (∀ w ∈ (after b4 tabS).mem, w.off + w.n ≤ 8 ∨ 112 ≤ w.off ∧ w.off + w.n ≤ 176) ∧
    WordW 0 112 (.reg .r14) (after b4 tabS) ∧ WordW 0 144 (.lit 0) (after b4 tabS) ∧
    WordW 0 152 (.lit 0) (after b4 tabS) ∧ WordW 0 160 (.lit 0) (after b4 tabS) ∧
    WordW 0 168 (.lit 0) (after b4 tabS) ∧
    (after b4 tabS).reg .rdi = some (.load 1 0 8) ∧ (after b4 tabS).reg .r14 = some (.load 1 16 8) ∧
    (after b4 tabS).reg .rsi = some (.reg .rbx) ∧ (after b4 tabS).reg .rdx = some (.reg .r12) ∧
    (after b4 tabS).reg .rcx = some (.ptr 0 144) ∧ (after b4 tabS).reg .rbp = some (.ptr 0 144) ∧
    Keeps (after b4 tabS) [.rbx, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 sF = some (after b5 sF,
    .call NativeRustcVmX64.Vm.Dot.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : missO (after b5 sF) (UW [96, 104]) = true ∧
    missR (after b5 sF) 144 176 = true ∧
    MidOk 272 0 slots (after b5 sF) = true ∧ WrOk (after b5 sF) [] = true ∧
    (∀ w ∈ (after b5 sF).mem, w.off + w.n ≤ 8 ∨ 96 ≤ w.off ∧ w.off + w.n ≤ 112) ∧
    WordW 0 96 (.reg .r14) (after b5 sF) ∧ WordW 0 104 (.reg .r15) (after b5 sF) ∧
    (after b5 sF).reg .rdi = some rdi5 ∧ (after b5 sF).reg .rsi = some rsi5 ∧
    (after b5 sF).reg .rdx = some (.reg .rbp) ∧ (after b5 sF).reg .rcx = some (.reg .rax) ∧
    (after b5 sF).reg .r15 = some (.lit 0) ∧
    Keeps (after b5 sF) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b6 : exec b6 formS = some (after b6 formS,
    .call NativeRustcVmX64.Vm.Evaluate.entryLabel) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : missO (after b6 formS) (UW [80, 88]) = true ∧
    MidOk 272 0 slots (after b6 formS) = true ∧
    WrOk (after b6 formS) [] = true ∧
    (∀ w ∈ (after b6 formS).mem, w.off + w.n ≤ 8 ∨ 80 ≤ w.off ∧ w.off + w.n ≤ 96) ∧
    WordW 0 80 (.reg .rax) (after b6 formS) ∧ WordW 0 88 (.reg .rdx) (after b6 formS) ∧
    (after b6 formS).reg .rsi = some (.ite (cF 0) (.reg .r15) (.load 1 0 8)) ∧
    (after b6 formS).reg .rdi =
      some (.ite (cF 0) (.lit 8) (.bin .add .W64 (.reg .r13) (.lit 18446744073709539760))) ∧
    (after b6 formS).reg .rdx = some (.reg .rbx) ∧ (after b6 formS).reg .rcx = some (.reg .r12) ∧
    (after b6 formS).reg .r14 = some (.lit 8) ∧
    Keeps (after b6 formS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b7 : exec b7 formS = some (after b7 formS,
    .call NativeRustcVmX64.Vm.Evaluate.entryLabel) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : missO (after b7 formS) (UW [176, 184]) = true ∧
    MidOk 272 0 slots (after b7 formS) = true ∧
    WrOk (after b7 formS) [] = true ∧
    (∀ w ∈ (after b7 formS).mem, w.off + w.n ≤ 8 ∨ 176 ≤ w.off ∧ w.off + w.n ≤ 192) ∧
    WordW 0 176 (.reg .rax) (after b7 formS) ∧ WordW 0 184 (.reg .rdx) (after b7 formS) ∧
    (after b7 formS).reg .rsi = some (.ite (cF 5928) (.reg .r15) (.load 1 5928 8)) ∧
    (after b7 formS).reg .rdi =
      some (.ite (cF 5928) (.reg .r14) (.bin .add .W64 (.reg .r13) (.lit 18446744073709545688))) ∧
    (after b7 formS).reg .rdx = some (.reg .rbx) ∧ (after b7 formS).reg .rcx = some (.reg .r12) ∧
    Keeps (after b7 formS) csR = true := by
  decide +kernel

public theorem exit_b8 : exec b8 formS = some (after b8 formS,
    .call NativeRustcVmX64.Vm.Evaluate.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : missO (after b8 formS) (UW [192, 200]) = true ∧
    MidOk 272 0 slots (after b8 formS) = true ∧
    WrOk (after b8 formS) [] = true ∧
    (∀ w ∈ (after b8 formS).mem, w.off + w.n ≤ 8 ∨ 192 ≤ w.off ∧ w.off + w.n ≤ 208) ∧
    WordW 0 192 (.reg .rax) (after b8 formS) ∧ WordW 0 200 (.reg .rdx) (after b8 formS) ∧
    (after b8 formS).reg .rsi = some (.ite (cF 11856) (.reg .r15) (.load 1 11856 8)) ∧
    (after b8 formS).reg .rdi =
      some (.ite (.cmp .ult .W64 (.load 1 11856 8) (.lit 149)) (.reg .r13) (.lit 8)) ∧
    (after b8 formS).reg .rdx = some (.reg .rbx) ∧ (after b8 formS).reg .rcx = some (.reg .r12) ∧
    Keeps (after b8 formS) csR = true := by
  decide +kernel

public theorem exit_b9 : exec b9 wS = some (after b9 wS,
    .call NativeRustcVmX64.Vm.Dot.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : missO (after b9 wS) (UW [64, 72]) = true ∧
    MidOk 272 0 slots (after b9 wS) = true ∧ WrOk (after b9 wS) [] = true ∧
    (∀ w ∈ (after b9 wS).mem, w.off + w.n ≤ 8 ∨ 64 ≤ w.off ∧ w.off + w.n ≤ 80 ∨
      208 ≤ w.off ∧ w.off + w.n ≤ 224) ∧
    WordW 0 208 (.reg .rax) (after b9 wS) ∧ WordW 0 216 (.reg .rdx) (after b9 wS) ∧
    WordW 0 72 (.load 2 0 8) (after b9 wS) ∧ WordW 0 64 (.load 2 8 8) (after b9 wS) ∧
    (after b9 wS).reg .rdi = some (.load 0 32 8) ∧ (after b9 wS).reg .rsi = some (.lit 3) ∧
    (after b9 wS).reg .rdx = some (.ptr 0 176) ∧ (after b9 wS).reg .rcx = some (.lit 3) ∧
    (after b9 wS).reg .r12 = some (.load 0 136 8) ∧
    Keeps (after b9 wS) [.rbx, .rbp, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b10 : exec b10 ptS = some (after b10 ptS,
    .call NativeRustcVmX64.Vm.BufEW30Extend.entryLabel) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : missO (after b10 ptS) (UW []) = true ∧
    MidOk 272 0 slots (after b10 ptS) = true ∧
    WrOk (after b10 ptS) [2] = true ∧
    (∀ w ∈ (after b10 ptS).mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 2 ∧ w.off + w.n ≤ 8)) ∧
    WordW 2 0 (.lit 0) (after b10 ptS) ∧
    (after b10 ptS).reg .rbx = some (.load 0 16 8) ∧ (after b10 ptS).reg .rbp = some (.load 0 112 8) ∧
    (after b10 ptS).reg .r14 = some (.reg .rax) ∧ (after b10 ptS).reg .r15 = some (.reg .r13) ∧
    (after b10 ptS).reg .r13 = some (.reg .rdx) ∧ (after b10 ptS).reg .rdi = some (.load 0 16 8) ∧
    (after b10 ptS).reg .rsi = some (.load 0 40 8) ∧ (after b10 ptS).reg .rdx = some rdx10 ∧
    Keeps (after b10 ptS) [.r12] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 sF = some (after b11 sF, .cond cAl NativeRustcVmX64.Vm.TableTerms.label_6) :=
  run_b11.trans (by rw [after_eq run_b11]; rfl)
public theorem ok_b11 : MidOk 272 8 slots (after b11 sF) = true ∧ (after b11 sF).mem = [] ∧
    Keeps (after b11 sF) csR = true := by
  decide +kernel

public theorem exit_b12 : exec b12 sF = some (after b12 sF,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : missO (after b12 sF) (UW []) = true ∧
    MidOk 272 0 slots (after b12 sF) = true ∧ WrOk (after b12 sF) [] = true ∧
    (∀ w ∈ (after b12 sF).mem, w.off + w.n ≤ 8) ∧
    (after b12 sF).reg .rdi = some (.load 0 72 8) ∧ (after b12 sF).reg .rsi = some (.load 0 64 8) ∧
    (after b12 sF).reg .rdx = some (.bin .xor .W64 (.reg .r14) (.load 0 80 8)) ∧
    (after b12 sF).reg .rcx = some (.bin .xor .W64 (.reg .r13) (.load 0 88 8)) ∧
    (after b12 sF).reg .r14 = some (.bin .xor .W64 (.reg .r14) (.load 0 80 8)) ∧
    (after b12 sF).reg .r13 = some (.bin .xor .W64 (.reg .r13) (.load 0 88 8)) ∧
    Keeps (after b12 sF) [.rbx, .rbp, .r12, .r15] = true := by
  decide +kernel

public theorem exit_b13 : exec b13 sF = some (after b13 sF, .cond c13 NativeRustcVmX64.Vm.TableTerms.label_1) :=
  run_b13.trans (by rw [after_eq run_b13]; rfl)
public theorem ok_b13 : missO (after b13 sF) (UW [16]) = true ∧
    MidOk 272 8 slots (after b13 sF) = true ∧ WrOk (after b13 sF) [] = true ∧
    (∀ w ∈ (after b13 sF).mem, 16 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    WordW 0 16 (.bin .add .W64 (.lit 1968) (.reg .rbx)) (after b13 sF) ∧
    (after b13 sF).reg .rcx = some (.bin .xor .W64 (.load 0 128 8) (.reg .rdx)) ∧
    (after b13 sF).reg .rdx = some (.bin .xor .W64 (.load 0 120 8) (.reg .rax)) ∧
    (after b13 sF).reg .r15 = some (.bin .add .W64 (.load 0 96 8) (.load 0 104 8)) ∧
    (after b13 sF).reg .rax = some (.bin .add .W64 (.lit 8) (.reg .r12)) ∧
    (after b13 sF).reg .r12 = some (.bin .add .W64 (.lit 8) (.reg .r12)) ∧
    (after b13 sF).reg .r13 = some (.bin .add .W64 (.lit 17784) (.reg .r15)) ∧
    (after b13 sF).reg .r14 = some (.bin .add .W64 (.lit 40) (.reg .rbp)) ∧
    (after b13 sF).reg .rbx = some (.bin .add .W64 (.lit 1968) (.reg .rbx)) ∧
    (after b13 sF).reg .rbp = some (.label tablesL) := by
  decide +kernel

public theorem exit_b14 : exec b14 outS = some (after b14 outS, .jump NativeRustcVmX64.Vm.TableTerms.label_7) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : missO (after b14 outS) (UW []) = true ∧
    MidOk 272 8 slots (after b14 outS) = true ∧
    WrOk (after b14 outS) [1] = true ∧ (∀ w ∈ (after b14 outS).mem, w.r = 1) ∧
    WordW 1 0 (.lit 1) (after b14 outS) ∧ WordW 1 8 (.reg .rdx) (after b14 outS) ∧
    WordW 1 16 (.reg .rcx) (after b14 outS) := by
  decide +kernel

public theorem exit_b15 : exec b15 outS = some (after b15 outS, .fall) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : missO (after b15 outS) (UW []) = true ∧
    MidOk 272 8 slots (after b15 outS) = true ∧
    WrOk (after b15 outS) [1] = true ∧ (∀ w ∈ (after b15 outS).mem, w.r = 1) ∧
    WordW 1 0 (.lit 0) (after b15 outS) := by
  decide +kernel

public theorem exit_b16 : exec b16 sF = some (after b16 sF, .ret (.load 0 272 8)) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : EpiOk 272 slots (after b16 sF) = true ∧ (after b16 sF).mem = [] := by
  decide +kernel

end

end NativeRustcVmX64.Tables.TableTerms
