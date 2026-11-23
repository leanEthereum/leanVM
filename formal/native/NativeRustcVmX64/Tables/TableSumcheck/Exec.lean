module

public import NativeRustcVmX64.Tables.TableTerms.Body
public import NativeRustcVmX64.Code.Vm.TableSumcheck
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TableSumcheck.Names
public import NativeRustcVmX64.Code.Vm.TableTerms.Names
public import NativeRustcVmX64.Code.Vm.TableWeights.Names
public meta import NativeRustcVmX64.Code.Vm.TableSumcheck

/-!
# `table_sumcheck`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 736-byte frame below the entry's RSP and the return address (`Frame`, `F = 736`:
RSP at offset `40` in the body; `table_terms`' return address at `0` below its four stack
arguments at `8`, `sumcheck`'s at `16` below its argument `n` at `24`, `table_weights`' at `32`):
the final claim's limb `0` at `48`, the constraint powers at `56`, the form powers at `64`, the
bus at `72`, the `TState` at `80`, `table_terms`' `Option<EW>` at `88`, the thirty challenges at
`112`, the sumcheck's `Option<EW>` at `592` (the weights at `592` after it), the pushed registers
from `688`. Region 1 the two stack arguments (the target's limb `1`, the evaluations) above the
return address, at the frame's offsets `744`, `752` (aliases).

- `entryS` (`b0`): the frame, region 1 the heights (RSI).
- `argS` (`b1`, `b10`, `b11`): the frame, the arguments.
- `retS` (`b2`): after `sumcheck`, RSP at `24`.
- `sF` (`b3` to `b6`, `b8`, `b12` to `b15`): the frame.
- `swapS` (`b7`): no frame; regions 0 to 2 the challenges at R15 (two), RSI, RAX + R8.
- `oneS` (`b9`): no frame; regions 0, 1 the challenges at RSP + 72 + 16 RCX and RAX - 16 (RCX + 1).
-/

namespace NativeRustcVmX64.Tables.TableSumcheck

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TableSumcheck
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck NativeRustcVmX64.Tables.Body

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(728, .rbp), (720, .r15), (712, .r14), (704, .r13), (696, .r12), (688, .rbx)]

/-- `RAX + R8` in `b7`: the challenge `n - 2 - i`. -/
def hiA : Sym :=
  .bin .add .W64 (.reg .rax) (.bin .shl .W64 (.bin .xor .W64 (.reg .rcx) (.reg .rdi)) (.lit 4))

/-- `RSP + 16 RCX` in `b9`: the challenge `i`, minus `72`. -/
def loA : Sym := .bin .add .W64 (.reg .rsp) (.bin .shl .W64 (.reg .rcx) (.lit 4))

/-- `RAX + 16 (¬RCX)` in `b9`: the challenge `n - 1 - i`. -/
def notA : Sym := .bin .add .W64 (.reg .rax) (.bin .shl .W64 (.un .not .W64 (.reg .rcx)) (.lit 4))

/-- `a > b`, unsigned, as `cmp`/`ja` test it. -/
def gt (a b : Sym) : SBool := .and (.not (.cmp .ult .W64 a b)) (.not (.cmp .eq .W64 a b))

/-- The larger of `a` and `b`, as `cmp`/`cmova` compute it. -/
def mx (a b : Sym) : Sym := .ite (gt b a) b a

/-- Height `i`. -/
def hS (i : Nat) : Sym := .load 1 (8 * i) 8

/-- The heights' maximum, `n`. -/
def R13 : Sym := mx (mx (mx (mx (mx (hS 0) (hS 1)) (hS 2)) (hS 3)) (hS 4)) (hS 5)

/-- `test %al, %al`-like tests of a byte: zero. -/
def c2 : SBool := .not (.cmp .eq .W32 (.load 0 592 4) (.lit 1))

/-- The callee-saved registers. -/
abbrev csR : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- The final check's sum: `(claim.c1 ^ final.c1) | (claim.c0 ^ final.c0)`. -/
def chk : Sym := .bin .or .W64 (.bin .xor .W64 (.reg .r14) (.load 0 104 8))
  (.bin .xor .W64 (.load 0 48 8) (.load 0 96 8))

def entryS : SState := init [744, 48] [(.rsp, .ptr 0 736)] [] [] [(.reg .rsi, 1, 0)]
def argS : SState :=
  init [744, 16] [(.rsp, .ptr 0 40)] [] [] [(.ptr 0 744, 1, 0), (.ptr 0 752, 1, 8)]
def retS : SState := init [744] [(.rsp, .ptr 0 24)]
def sF : SState := init [744] [(.rsp, .ptr 0 40)]
def busS : SState :=
  init [744, 106712] [(.rsp, .ptr 0 40)] [] [] [(.load 0 72 8, 1, 0)]
def tS : SState := init [744] [(.rsp, .ptr 0 8)]
def swapS : SState := init [32, 16, 16] [] [] [] [(.reg .r15, 0, 0), (.reg .rsi, 1, 0), (hiA, 2, 0)]
def oneS : SState := init [16, 16] [] [] [] [(loA, 0, -72), (notA, 1, 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 argS
sym_block run_b2 := exec b2 retS
sym_block run_b3 := exec b3 sF
sym_block run_b4 := exec b4 sF
sym_block run_b5 := exec b5 sF
sym_block run_b6 := exec b6 sF
sym_block run_b7 := exec b7 swapS
sym_block run_b8 := exec b8 sF
sym_block run_b9 := exec b9 oneS
sym_block run_b10 := exec b10 busS
sym_block run_b11 := exec b11 argS
sym_block run_b12 := exec b12 tS
sym_block run_b13 := exec b13 sF
sym_block run_b14 := exec b14 sF
sym_block run_b15 := exec b15 sF


section
open NativeRustcVmX64.Transcript (after after_eq)

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (gt R13 (.lit 30)) NativeRustcVmX64.Vm.TableSumcheck.label_11) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : ProOk 736 40 slots (after b0 entryS) = true ∧
    WrOk (after b0 entryS) [] = true ∧
    (after b0 entryS).reg .r13 = some R13 ∧ (after b0 entryS).reg .rbp = some (.reg .rcx) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdx) ∧ (after b0 entryS).reg .rbx = some (.reg .rsi) ∧
    (after b0 entryS).reg .r10 = some (.reg .rdi) ∧ (after b0 entryS).reg .r8 = some (.reg .r8) ∧
    (after b0 entryS).reg .r9 = some (.reg .r9) := by
  decide +kernel

public theorem exit_b1 : exec b1 argS = some (after b1 argS,
    .call NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk 736 16 slots (after b1 argS) = true ∧ WrOk (after b1 argS) [] = true ∧
    (∀ w ∈ (after b1 argS).mem, w.r = 0 ∧ w.off + w.n ≤ 88) ∧
    WordW 0 24 (.reg .r13) (after b1 argS) ∧ WordW 0 80 (.reg .r10) (after b1 argS) ∧
    (after b1 argS).reg .rcx = some (.load 1 0 8) ∧ (after b1 argS).reg .rdx = some (.reg .r9) ∧
    (after b1 argS).reg .rsi = some (.reg .r10) ∧ (after b1 argS).reg .rdi = some (.ptr 0 592) ∧
    (after b1 argS).reg .r8 = some (.lit 4) ∧ (after b1 argS).reg .r9 = some (.ptr 0 112) ∧
    (after b1 argS).reg .r12 = some (.reg .r8) ∧ (after b1 argS).reg .r15 = some (.ptr 0 112) ∧
    Keeps (after b1 argS) [.rbx, .rbp, .r13, .r14] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 retS = some (after b2 retS, .cond c2 NativeRustcVmX64.Vm.TableSumcheck.label_11) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 736 40 slots (after b2 retS) = true ∧ (after b2 retS).mem = [] ∧
    Keeps (after b2 retS) csR = true := by
  decide +kernel

public theorem exit_b3 : exec b3 sF = some (after b3 sF,
    .cond (.cmp .eq .W64 (.bin .shr .W64 (.reg .r13) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.TableSumcheck.label_9) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 736 40 slots (after b3 sF) = true ∧ WrOk (after b3 sF) [] = true ∧
    (∀ w ∈ (after b3 sF).mem, 56 ≤ w.off ∧ w.off + w.n ≤ 80) ∧
    WordW 0 56 (.reg .rbp) (after b3 sF) ∧ WordW 0 64 (.reg .r12) (after b3 sF) ∧
    WordW 0 72 (.reg .r14) (after b3 sF) ∧
    (after b3 sF).reg .rdx = some (.bin .shr .W64 (.reg .r13) (.lit 1)) ∧
    Keeps (after b3 sF) csR = true := by
  decide +kernel

public theorem exit_b4 : exec b4 sF = some (after b4 sF,
    .cond (.not (.cmp .eq .W64 (.reg .rdx) (.lit 1))) NativeRustcVmX64.Vm.TableSumcheck.label_5) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 736 40 slots (after b4 sF) = true ∧ (after b4 sF).mem = [] ∧
    (after b4 sF).reg .rcx = some (.bin .shl .W64 (.reg .r13) (.lit 4)) ∧
    (after b4 sF).reg .rax =
      some (.bin .add .W64 (.lit 72) (.bin .add .W64 (.ptr 0 40) (.bin .shl .W64 (.reg .r13) (.lit 4)))) ∧
    (after b4 sF).reg .rdx = some (.reg .rdx) ∧ Keeps (after b4 sF) csR = true := by
  decide +kernel

public theorem exit_b5 : exec b5 sF = some (after b5 sF, .jump NativeRustcVmX64.Vm.TableSumcheck.label_8) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 736 40 slots (after b5 sF) = true ∧ (after b5 sF).mem = [] ∧
    (after b5 sF).reg .rcx = some (.lit 0) ∧ (after b5 sF).reg .rax = some (.reg .rax) ∧
    Keeps (after b5 sF) csR = true := by
  decide +kernel

public theorem exit_b6 : exec b6 sF = some (after b6 sF, .fall) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 736 40 slots (after b6 sF) = true ∧ (after b6 sF).mem = [] ∧
    (after b6 sF).reg .rcx = some (.lit 0) ∧
    (after b6 sF).reg .rdx = some (.bin .and .W32 (.reg .rdx) (.lit 14)) ∧
    (after b6 sF).reg .rsi =
      some (.bin .add .W64 (.lit 18446744073709551600) (.bin .add .W64 (.reg .rcx) (.reg .r15))) ∧
    (after b6 sF).reg .rdi = some (.lit 1152921504606846974) ∧
    (after b6 sF).reg .rax = some (.reg .rax) ∧ Keeps (after b6 sF) csR = true := by
  decide +kernel

public theorem exit_b7 : exec b7 swapS = some (after b7 swapS,
    .cond (.not (.cmp .eq .W64 (.reg .rdx) (.bin .add .W64 (.lit 2) (.reg .rcx))))
      NativeRustcVmX64.Vm.TableSumcheck.label_6) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 :
    (∀ w ∈ (after b7 swapS).mem, (w.r = 0 ∧ w.off + w.n ≤ 32) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 16)) ∧
    WordW 0 0 (.load 1 0 8) (after b7 swapS) ∧ WordW 0 8 (.load 1 8 8) (after b7 swapS) ∧
    WordW 1 0 (.load 0 0 8) (after b7 swapS) ∧ WordW 1 8 (.load 0 8 8) (after b7 swapS) ∧
    WordW 0 16 (.load 2 0 8) (after b7 swapS) ∧ WordW 0 24 (.load 2 8 8) (after b7 swapS) ∧
    WordW 2 0 (.load 0 16 8) (after b7 swapS) ∧ WordW 2 8 (.load 0 24 8) (after b7 swapS) ∧
    (after b7 swapS).reg .rcx = some (.bin .add .W64 (.lit 2) (.reg .rcx)) ∧
    (after b7 swapS).reg .r15 = some (.bin .add .W64 (.lit 32) (.reg .r15)) ∧
    (after b7 swapS).reg .rsi = some (.bin .add .W64 (.lit 18446744073709551584) (.reg .rsi)) ∧
    (after b7 swapS).reg .rsp = some (.reg .rsp) ∧ (after b7 swapS).reg .rax = some (.reg .rax) ∧
    (after b7 swapS).reg .rdx = some (.reg .rdx) ∧ (after b7 swapS).reg .rdi = some (.reg .rdi) ∧
    Keeps (after b7 swapS) [.rbx, .rbp, .r12, .r13] = true := by
  decide +kernel

public theorem exit_b8 : exec b8 sF = some (after b8 sF,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .r13) (.lit 2)) (.lit 0)) NativeRustcVmX64.Vm.TableSumcheck.label_9) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 736 40 slots (after b8 sF) = true ∧ (after b8 sF).mem = [] ∧
    (after b8 sF).reg .rcx = some (.reg .rcx) ∧ (after b8 sF).reg .rax = some (.reg .rax) ∧
    Keeps (after b8 sF) csR = true := by
  decide +kernel

public theorem exit_b9 : exec b9 oneS = some (after b9 oneS, .fall) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 :
    (∀ w ∈ (after b9 oneS).mem, (w.r = 0 ∧ w.off + w.n ≤ 16) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    WordW 0 0 (.load 1 0 8) (after b9 oneS) ∧ WordW 0 8 (.load 1 8 8) (after b9 oneS) ∧
    WordW 1 0 (.load 0 0 8) (after b9 oneS) ∧ WordW 1 8 (.load 0 8 8) (after b9 oneS) ∧
    (after b9 oneS).reg .rsp = some (.reg .rsp) ∧ Keeps (after b9 oneS) csR = true := by
  decide +kernel

public theorem exit_b10 : exec b10 busS = some (after b10 busS,
    .call NativeRustcVmX64.Vm.TableWeights.entryLabel) :=
  run_b10.trans (by rw [after_eq run_b10])
public theorem ok_b10 : MidOk 736 32 slots (after b10 busS) = true ∧
    WrOk (after b10 busS) [] = true ∧
    (∀ w ∈ (after b10 busS).mem, w.r = 0 ∧ w.off + w.n ≤ 56) ∧
    WordW 0 48 (.load 0 600 8) (after b10 busS) ∧
    (after b10 busS).reg .r14 = some (.load 0 608 8) ∧
    (after b10 busS).reg .rcx = some (.ite (.cmp .ult .W64 (.load 1 106704 8) (.lit 64))
      (.load 1 106704 8) (.lit 0)) ∧
    (after b10 busS).reg .rdx = some (.ite (.cmp .ult .W64 (.load 1 106704 8) (.lit 64))
      (.bin .add .W64 (.load 0 72 8) (.lit 106712)) (.lit 8)) ∧
    (after b10 busS).reg .rsi = some (.reg .rbx) ∧ (after b10 busS).reg .rdi = some (.ptr 0 592) ∧
    (after b10 busS).reg .rbp = some (.load 0 72 8) ∧ (after b10 busS).reg .r8 = some (.ptr 0 112) ∧
    (after b10 busS).reg .r9 = some (.reg .r13) ∧ (after b10 busS).reg .r12 = some (.ptr 0 592) ∧
    (after b10 busS).reg .r15 = some (.ptr 0 112) ∧
    Keeps (after b10 busS) [.rbx, .r13] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 argS = some (after b11 argS,
    .call NativeRustcVmX64.Vm.TableTerms.entryLabel) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : MidOk 736 0 slots (after b11 argS) = true ∧
    WrOk (after b11 argS) [] = true ∧
    (∀ w ∈ (after b11 argS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    WordW 0 8 (.reg .rbx) (after b11 argS) ∧ WordW 0 16 (.reg .rbp) (after b11 argS) ∧
    WordW 0 24 (.reg .r12) (after b11 argS) ∧ WordW 0 32 (.load 1 8 8) (after b11 argS) ∧
    (after b11 argS).reg .rdi = some (.ptr 0 88) ∧ (after b11 argS).reg .rsi = some (.load 0 80 8) ∧
    (after b11 argS).reg .rdx = some (.load 0 56 8) ∧ (after b11 argS).reg .rcx = some (.load 0 64 8) ∧
    (after b11 argS).reg .r8 = some (.reg .r15) ∧ (after b11 argS).reg .r9 = some (.reg .r13) ∧
    Keeps (after b11 argS) csR = true := by
  decide +kernel

public theorem exit_b12 : exec b12 tS = some (after b12 tS,
    .cond (.cmp .eq .W8 (.load 0 88 1) (.lit 0)) NativeRustcVmX64.Vm.TableSumcheck.label_11) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : MidOk 736 40 slots (after b12 tS) = true ∧ (after b12 tS).mem = [] ∧
    Keeps (after b12 tS) csR = true := by
  decide +kernel

public theorem exit_b13 : exec b13 sF = some (after b13 sF, .jump NativeRustcVmX64.Vm.TableSumcheck.label_12) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : MidOk 736 40 slots (after b13 sF) = true ∧ (after b13 sF).mem = [] ∧
    (after b13 sF).reg .rax = some (.bin .merge .W8 (.bin .xor .W64 (.load 0 48 8) (.load 0 96 8))
      (.ite (.cmp .eq .W64 chk (.lit 0)) (.lit 1) (.lit 0))) := by
  decide +kernel

public theorem exit_b14 : exec b14 sF = some (after b14 sF, .fall) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : MidOk 736 40 slots (after b14 sF) = true ∧ (after b14 sF).mem = [] ∧
    (after b14 sF).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem exit_b15 : exec b15 sF = some (after b15 sF, .ret (.load 0 736 8)) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : EpiOk 736 slots (after b15 sF) = true ∧ (after b15 sF).mem = [] ∧
    (after b15 sF).reg .rax = some (.reg .rax) := by
  decide +kernel

end

end NativeRustcVmX64.Tables.TableSumcheck
