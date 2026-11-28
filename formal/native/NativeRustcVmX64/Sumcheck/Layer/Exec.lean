module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names
public meta import NativeRustcVmX64.Code.Vm.SumcheckOfVerifyLayer
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `sumcheck` with `verify_layer`'s closure: its blocks, run by the symbolic executor (x86-64)

Region 0 is the 192-byte frame below the entry's RSP and the return address (`F = 192`: RSP at
offset `8` in the body, a callee's return address at `0`): the output's address at `16`, the
point's at `24`, `|pt|` at `32`, `eq` at `40` (24 bytes), the message at `64` (80 bytes), the
pushed registers from `144`. Region 1 is the two stack arguments above the return address (the
slots' address, `n`; 16 bytes), reached through RSP by aliases (`argAl`).

- `entryS`, at the entry (`b0`, `b1`);
- `bodyS`, in the body: the loop's head `b2`, `b5`, `b6` (the call), the test `b7`, `b8`,
  `b10`;
- `ptS`, at `b3`: region 1 the point's coordinate `i` (its address the frame's word at `24` plus
  R13, an alias);
- `slotS`, at `b9`: region 1 the slot at R15;
- `outS`, at the exits `b11`, `b12`, then `b13`: region 1 the output, its address the frame's
  word at `16` (an alias).
-/

namespace NativeRustcVmX64.Sumcheck.Layer

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfVerifyLayer
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(184, .rbp), (176, .r15), (168, .r14), (160, .r13), (152, .r12), (144, .rbx)]

/-- The stack arguments' words through the frame's region: region 1. -/
def argAl : List (Sym × Nat × Int) := [(.ptr 0 200, 1, 0), (.ptr 0 208, 1, 8)]

/-- At the entry: the frame, the stack arguments. -/
def entryS : SState := init [200, 16] [(.rsp, .ptr 0 192)] (aliases := argAl)

/-- In the body. -/
def bodyS : SState := init [200, 16] [(.rsp, .ptr 0 8)] (aliases := argAl)

/-- At `b3`: the point's coordinate `i`, its address the frame's word at `24` plus R13. -/
def ptS : SState := init [200, 16] [(.rsp, .ptr 0 8)]
  (aliases := [(.bin .add .W64 (.load 0 24 8) (.reg .r13), 1, 0)])

/-- At `b9`: the slot at R15. -/
def slotS : SState := init [200, 16] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]

/-- At the exits: the output at the frame's word at `16`. -/
def outS : SState := init [200, 24] [(.rsp, .ptr 0 8)] (aliases := [(.load 0 16 8, 1, 0)])

/-- `b0`'s exit: no slot. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 (.load 1 8 8) (.load 1 8 8)) (.lit 0)

/-- `b2`'s exit: no coordinate `i`. -/
def c2 : SBool := .not (.cmp .ult .W64 (.reg .r14) (.load 0 32 8))

/-- `test %al, %al`, zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- `b10`'s exit: another round. -/
def c10 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .r15)) (.reg .rbx))

/-- What a block keeps: the given registers' atoms. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 ptS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 bodyS
sym_block run_b9 := exec b9 slotS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 outS
sym_block run_b12 := exec b12 outS
sym_block run_b13a := exec b13 (after b11 outS)
sym_block run_b13b := exec b13 (after b12 outS)


public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_8) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : ProOk 192 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧ WordW 0 16 (.reg .rdi) (after b0 entryS) ∧
    WordW 0 24 (.reg .r8) (after b0 entryS) ∧ WordW 0 32 (.reg .r9) (after b0 entryS) ∧
    (after b0 entryS).reg .rax = some (.reg .rdx) ∧ (after b0 entryS).reg .rcx = some (.reg .rcx) := by
  decide +kernel
public theorem exit_b1 : exec b1 (after b0 entryS) = some (after b1 (after b0 entryS), .fall) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : ProOk 192 8 slots (after b1 (after b0 entryS)) = true ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0) ∧
    WordW 0 16 (.reg .rdi) (after b1 (after b0 entryS)) ∧
    WordW 0 24 (.reg .r8) (after b1 (after b0 entryS)) ∧
    WordW 0 32 (.reg .r9) (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .rax = some (.reg .rdx) ∧
    (after b1 (after b0 entryS)).reg .rcx = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .rbx =
      some (.bin .add .W64 (.load 1 0 8) (.bin .shl .W64 (.load 1 8 8) (.lit 4))) ∧
    (after b1 (after b0 entryS)).reg .rbp = some (.ptr 0 64) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.reg .rsi) ∧
    (after b1 (after b0 entryS)).reg .r13 = some (.lit 0) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.lit 0) := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS, .cond c2 NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_3) :=
  run_b2.trans (by rw [after_eq run_b2]; rfl)
public theorem ok_b2 : MidOk 192 8 slots (after b2 bodyS) = true ∧ (after b2 bodyS).mem = [] ∧
    Keeps (after b2 bodyS) [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b3 : exec b3 ptS = some (after b3 ptS, .jump NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_5) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 192 8 slots (after b3 ptS) = true ∧
    (∀ w ∈ (after b3 ptS).mem, w.r = 0 ∧ 48 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    WordW 0 48 (.load 1 0 8) (after b3 ptS) ∧ WordW 0 56 (.load 1 8 8) (after b3 ptS) ∧
    (after b3 ptS).reg .rdx = some (.lit 1) ∧
    Keeps (after b3 ptS) [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b5 : exec b5 bodyS = some (after b5 bodyS, .fall) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 192 8 slots (after b5 bodyS) = true ∧ (after b5 bodyS).mem = [] ∧
    (after b5 bodyS).reg .rdx = some (.lit 0) ∧
    Keeps (after b5 bodyS) [.rax, .rcx, .rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b6 : exec b6 bodyS = some (after b6 bodyS,
    .call NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 192 0 slots (after b6 bodyS) = true ∧
    (∀ w ∈ (after b6 bodyS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off ∧ w.off + w.n ≤ 48)) ∧
    WordW 0 40 (.reg .rdx) (after b6 bodyS) ∧
    (after b6 bodyS).reg .rdi = some (.reg .r12) ∧ (after b6 bodyS).reg .rsi = some (.lit 3) ∧
    (after b6 bodyS).reg .rdx = some (.reg .rax) ∧ (after b6 bodyS).reg .rcx = some (.reg .rcx) ∧
    (after b6 bodyS).reg .r8 = some (.ptr 0 40) ∧ (after b6 bodyS).reg .r9 = some (.reg .rbp) ∧
    Keeps (after b6 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b7 : exec b7 bodyS = some (after b7 bodyS, .cond cAl NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_6) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem ok_b7 : MidOk 192 8 slots (after b7 bodyS) = true ∧ (after b7 bodyS).mem = [] ∧
    Keeps (after b7 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b8 : exec b8 bodyS = some (after b8 bodyS,
    .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 192 0 slots (after b8 bodyS) = true ∧
    (∀ w ∈ (after b8 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b8 bodyS).reg .rdi = some (.reg .r12) ∧
    (after b8 bodyS).reg .r15 = some (.bin .add .W64 (.load 1 0 8) (.reg .r13)) ∧
    Keeps (after b8 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b9 : exec b9 slotS = some (after b9 slotS,
    .call NativeRustcVmX64.Vm.PolyEval.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 192 0 slots (after b9 slotS) = true ∧
    (∀ w ∈ (after b9 slotS).mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    WordW 1 0 (.reg .rax) (after b9 slotS) ∧ WordW 1 8 (.reg .rdx) (after b9 slotS) ∧
    (after b9 slotS).reg .rdi = some (.reg .rbp) ∧ (after b9 slotS).reg .rsi = some (.lit 3) ∧
    (after b9 slotS).reg .rdx = some (.reg .rax) ∧ (after b9 slotS).reg .rcx = some (.reg .rdx) ∧
    (after b9 slotS).reg .r15 = some (.ptr 1 0) ∧
    Keeps (after b9 slotS) [.rbx, .rbp, .r12, .r13, .r14] = true := by
  decide +kernel
public theorem exit_b10 : exec b10 bodyS =
    some (after b10 bodyS, .cond c10 NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_2) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : MidOk 192 8 slots (after b10 bodyS) = true ∧ (after b10 bodyS).mem = [] ∧
    (after b10 bodyS).reg .rcx = some (.reg .rdx) ∧
    (after b10 bodyS).reg .r13 = some (.bin .add .W64 (.lit 16) (.reg .r13)) ∧
    (after b10 bodyS).reg .r14 = some (.bin .add .W64 (.reg .r14) (.lit 1)) ∧
    Keeps (after b10 bodyS) [.rax, .rbx, .rbp, .r12] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 outS = some (after b11 outS, .jump NativeRustcVmX64.Vm.SumcheckOfVerifyLayer.label_9) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem exit_b13a : exec b13 (after b11 outS) =
    some (after b13 (after b11 outS), .ret (.load 0 192 8)) :=
  run_b13a.trans (by rw [after_eq run_b13a])
public theorem ok_b13a : EpiOk 192 slots (after b13 (after b11 outS)) = true ∧
    (∀ w ∈ (after b13 (after b11 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    WordW 1 0 (.lit 1) (after b13 (after b11 outS)) ∧
    WordW 1 8 (.reg .rax) (after b13 (after b11 outS)) ∧
    WordW 1 16 (.reg .rcx) (after b13 (after b11 outS)) := by
  decide +kernel
public theorem exit_b12 : exec b12 outS = some (after b12 outS, .fall) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem exit_b13b : exec b13 (after b12 outS) =
    some (after b13 (after b12 outS), .ret (.load 0 192 8)) :=
  run_b13b.trans (by rw [after_eq run_b13b])
public theorem ok_b13b : EpiOk 192 slots (after b13 (after b12 outS)) = true ∧
    (∀ w ∈ (after b13 (after b12 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    WordW 1 0 (.lit 0) (after b13 (after b12 outS)) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.Layer
