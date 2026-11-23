module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain
public import NativeRustcVmX64.Code.Vm.PolyEval.Names
public import NativeRustcVmX64.Code.Vm.SpongeWSqueeze.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateSumcheckRoundPoly.Names
public meta import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `sumcheck` with `sumcheck_plain`'s closure: its blocks, run by the symbolic executor (x86-64)

Region 0 is the 176-byte frame below the entry's RSP and the return address (`F = 176`: RSP at
offset `8` in the body, a callee's return address at `0`): the output's address at `16`, the
message at `24` (80 bytes), `eq` at `104` (24 bytes), the pushed registers from `128`.

- `entryS`, at the entry (`b0`, `b1`): region 1 the stack argument `n` (`.ptr 0 184`, the word
  above the return address, its alias);
- `bodyS`, in the body: the loop's head `b2`, the tests `b3`, `b6`, the call `b4`;
- `slotS`, at `b5`: region 1 the slot at R14;
- `outS`, at the exits `b7`, `b8`, then `b9`: region 1 the output, its address the frame's word at
  `16` (an alias).
-/

namespace NativeRustcVmX64.Sumcheck.Plain

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(168, .rbp), (160, .r15), (152, .r14), (144, .r13), (136, .r12), (128, .rbx)]

/-- At the entry: the frame, the stack argument. -/
def entryS : SState := init [184, 8] [(.rsp, .ptr 0 176)] (aliases := [(.ptr 0 184, 1, 0)])

/-- In the body. -/
def bodyS : SState := init [184] [(.rsp, .ptr 0 8)]

/-- At `b5`: the frame, the slot at R14. -/
def slotS : SState := init [184, 16] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

/-- At the exits: the frame, the output at the frame's word at `16`. -/
def outS : SState := init [184, 24] [(.rsp, .ptr 0 8)] (aliases := [(.load 0 16 8, 1, 0)])

/-- `b0`'s exit: no slot. -/
def c0 : SBool := .cmp .eq .W64 (.bin .and .W64 (.load 1 0 8) (.load 1 0 8)) (.lit 0)

/-- `test %al, %al`, zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- `b6`'s exit: another round. -/
def c6 : SBool := .not (.cmp .eq .W64 (.bin .add .W64 (.lit 16) (.reg .r14)) (.reg .rbx))

/-- What a block keeps: the given registers' atoms. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 (after b0 entryS)
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 slotS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 outS
sym_block run_b8 := exec b8 outS
sym_block run_b9a := exec b9 (after b7 outS)
sym_block run_b9b := exec b9 (after b8 outS)

public theorem exit_b0 : exec b0 entryS =
    some (after b0 entryS, .cond c0 NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_5) :=
  run_b0.trans (by rw [after_eq run_b0]; rfl)
public theorem ok_b0 : ProOk 176 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0) ∧ WordW 0 16 (.reg .rdi) (after b0 entryS) ∧
    (after b0 entryS).reg .rax = some (.reg .rdx) ∧
    (after b0 entryS).reg .rcx = some (.reg .rcx) := by
  decide +kernel
public theorem exit_b1 : exec b1 (after b0 entryS) = some (after b1 (after b0 entryS), .fall) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : ProOk 176 8 slots (after b1 (after b0 entryS)) = true ∧
    (∀ w ∈ (after b1 (after b0 entryS)).mem, w.r = 0) ∧
    WordW 0 16 (.reg .rdi) (after b1 (after b0 entryS)) ∧
    (after b1 (after b0 entryS)).reg .rax = some (.reg .rdx) ∧
    (after b1 (after b0 entryS)).reg .rcx = some (.reg .rcx) ∧
    (after b1 (after b0 entryS)).reg .rbx =
      some (.bin .add .W64 (.reg .r9) (.bin .shl .W64 (.load 1 0 8) (.lit 4))) ∧
    (after b1 (after b0 entryS)).reg .rbp = some (.ptr 0 24) ∧
    (after b1 (after b0 entryS)).reg .r12 = some (.reg .rsi) ∧
    (after b1 (after b0 entryS)).reg .r13 = some (.ptr 0 104) ∧
    (after b1 (after b0 entryS)).reg .r14 = some (.reg .r9) ∧
    (after b1 (after b0 entryS)).reg .r15 = some (.reg .r8) := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS,
    .call NativeRustcVmX64.Vm.TStateSumcheckRoundPoly.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : MidOk 176 0 slots (after b2 bodyS) = true ∧
    (∀ w ∈ (after b2 bodyS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 104 ≤ w.off ∧ w.off + w.n ≤ 112)) ∧
    WordW 0 104 (.lit 0) (after b2 bodyS) ∧
    (after b2 bodyS).reg .rdi = some (.reg .r12) ∧ (after b2 bodyS).reg .rsi = some (.reg .r15) ∧
    (after b2 bodyS).reg .rdx = some (.reg .rax) ∧ (after b2 bodyS).reg .rcx = some (.reg .rcx) ∧
    (after b2 bodyS).reg .r8 = some (.reg .r13) ∧ (after b2 bodyS).reg .r9 = some (.reg .rbp) ∧
    Keeps (after b2 bodyS) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b3 : exec b3 bodyS =
    some (after b3 bodyS, .cond cAl NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_3) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem ok_b3 : MidOk 176 8 slots (after b3 bodyS) = true ∧ (after b3 bodyS).mem = [] ∧
    Keeps (after b3 bodyS) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b4 : exec b4 bodyS = some (after b4 bodyS,
    .call NativeRustcVmX64.Vm.SpongeWSqueeze.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 176 0 slots (after b4 bodyS) = true ∧
    (∀ w ∈ (after b4 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b4 bodyS).reg .rdi = some (.reg .r12) ∧
    Keeps (after b4 bodyS) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel
public theorem exit_b5 : exec b5 slotS = some (after b5 slotS,
    .call NativeRustcVmX64.Vm.PolyEval.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 176 0 slots (after b5 slotS) = true ∧
    (∀ w ∈ (after b5 slotS).mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 16)) ∧
    WordW 1 0 (.reg .rax) (after b5 slotS) ∧ WordW 1 8 (.reg .rdx) (after b5 slotS) ∧
    (after b5 slotS).reg .rdi = some (.reg .rbp) ∧ (after b5 slotS).reg .rsi = some (.reg .r15) ∧
    (after b5 slotS).reg .rdx = some (.reg .rax) ∧ (after b5 slotS).reg .rcx = some (.reg .rdx) ∧
    (after b5 slotS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b5 slotS) [.rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel
public theorem exit_b6 : exec b6 bodyS =
    some (after b6 bodyS, .cond c6 NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_2) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : MidOk 176 8 slots (after b6 bodyS) = true ∧ (after b6 bodyS).mem = [] ∧
    (after b6 bodyS).reg .rcx = some (.reg .rdx) ∧
    (after b6 bodyS).reg .r14 = some (.bin .add .W64 (.lit 16) (.reg .r14)) ∧
    Keeps (after b6 bodyS) [.rax, .rbx, .rbp, .r12, .r13, .r15] = true := by
  decide +kernel

public theorem exit_b7 : exec b7 outS = some (after b7 outS, .jump NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.label_6) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem exit_b9a : exec b9 (after b7 outS) =
    some (after b9 (after b7 outS), .ret (.load 0 176 8)) :=
  run_b9a.trans (by rw [after_eq run_b9a])
public theorem ok_b9a : EpiOk 176 slots (after b9 (after b7 outS)) = true ∧
    (∀ w ∈ (after b9 (after b7 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    WordW 1 0 (.lit 1) (after b9 (after b7 outS)) ∧
    WordW 1 8 (.reg .rax) (after b9 (after b7 outS)) ∧
    WordW 1 16 (.reg .rcx) (after b9 (after b7 outS)) := by
  decide +kernel
public theorem exit_b8 : exec b8 outS = some (after b8 outS, .fall) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem exit_b9b : exec b9 (after b8 outS) =
    some (after b9 (after b8 outS), .ret (.load 0 176 8)) :=
  run_b9b.trans (by rw [after_eq run_b9b])
public theorem ok_b9b : EpiOk 176 slots (after b9 (after b8 outS)) = true ∧
    (∀ w ∈ (after b9 (after b8 outS)).mem, w.r = 1 ∧ w.off + w.n ≤ 24) ∧
    WordW 1 0 (.lit 0) (after b9 (after b8 outS)) := by
  decide +kernel

end NativeRustcVmX64.Sumcheck.Plain
