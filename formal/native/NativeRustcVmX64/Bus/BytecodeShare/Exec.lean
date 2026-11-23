module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.BytecodeShare
public import NativeRustcVmX64.Code.Vm.BytecodeShare.Names
public import NativeRustcVmX64.Code.Vm.Dot.Names
public import NativeRustcVmX64.Code.Vm.EWMul.Names
public import NativeRustcVmX64.Code.Vm.EqKernel.Names
public import NativeRustcVmX64.Code.Vm.SumcheckOfSumcheckPlain.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public meta import NativeRustcVmX64.Code.Vm.BytecodeShare
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `bytecode_share`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 432-byte frame below the entry's RSP and the return address (`Frame`, `F = 432`:
RSP at offset `8` in the body, a callee's return address at `0`): the sumcheck's stack argument at
`8`, the value's limb `1` at `24`, the slot point (four elements) at `32`, the claim's limbs `1`,
`0` at `96`, `104`, the share's limbs `1`, `0` at `112`, `120`, the transcript calls' `Option<EW>`
and then the kernel (sixteen elements) at `128`, the six pushed registers from `384`.

- `entryS`, at the entry (`b0`); `bodyS`, in the body (every block but the ones below);
- `outS`: region 1 the output (RBX, 48 bytes; `b15`, the tag `0`);
- `pairS`: regions 1, 2 two elements of `bytecode_low` and of the point, at `R13 + RDI - 24`,
  `R12 + RDI - 24` (`b18`, the pair loop);
- `oneS`: regions 1, 2 one element each, at `R13 + 16 RDX`, `R12 + 16 RDX` (`b20`);
- `endS`: region 1 the output (RBX), region 2 the point's last four slots (RCX; `b21`).
-/

namespace NativeRustcVmX64.Bus.BytecodeShare

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BytecodeShare NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(424, .rbp), (416, .r15), (408, .r14), (400, .r13), (392, .r12), (384, .rbx)]

/-- At the entry: the frame. -/
def entryS : SState := init [440] [(.rsp, .ptr 0 432)]

/-- In the body: the frame. -/
def bodyS : SState := init [440] [(.rsp, .ptr 0 8)]

/-- In the body, the output (RBX). -/
def outS : SState := init [440, 48] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- The pair loop's source (`R13 + RDI`) and target (`R12 + RDI`), 24 bytes into their regions. -/
def srcP : Sym := .bin .add .W64 (.reg .r13) (.reg .rdi)
def dstP : Sym := .bin .add .W64 (.reg .r12) (.reg .rdi)

/-- In the pair loop: two elements of the source and of the target. -/
def pairS : SState :=
  init [440, 32, 32] [(.rsp, .ptr 0 8)] (aliases := [(srcP, (1, 24)), (dstP, (2, 24))])

/-- The odd element's source (`R13 + 16 RDX`) and target (`R12 + 16 RDX`). -/
def srcO : Sym := .bin .add .W64 (.reg .r13) (.bin .shl .W64 (.reg .rdx) (.lit 4))
def dstO : Sym := .bin .add .W64 (.reg .r12) (.bin .shl .W64 (.reg .rdx) (.lit 4))

/-- At the odd element: one element of the source and of the target. -/
def oneS : SState :=
  init [440, 16, 16] [(.rsp, .ptr 0 8)] (aliases := [(srcO, (1, 0)), (dstO, (2, 0))])

/-- At the end: the output (RBX), the point's last four slots (RCX). -/
def endS : SState := init [440, 48, 64] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.rcx, .ptr 2 0)]

/-- The registers a block keeps. -/
def KeepsB (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- The six callee-saved registers the body holds. -/
abbrev six : List Reg64 := [.rbx, .rbp, .r12, .r13, .r14, .r15]

/-- Every write in region 0, outside `[lo, hi)` but the callee's return address. -/
def WritesF (S : SState) (lo hi : Nat) : Prop :=
  ∀ w ∈ S.mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ lo ≤ w.off ∧ w.off + w.n ≤ hi)

instance (S : SState) (lo hi : Nat) : Decidable (WritesF S lo hi) := by
  unfold WritesF; infer_instance

/-- `nw` words of region `rd` at `od` copied from region `rs` at `os`. -/
def CopyW (S : SState) (rd od rs os nw : Nat) : Prop :=
  ∀ w < nw, ∀ t < 8, findWrite rd (od + 8 * w + t) S.mem = some (.load rs (os + 8 * w) 8, t)

instance (S : SState) (rd od rs os nw : Nat) : Decidable (CopyW S rd od rs os nw) := by
  unfold CopyW; infer_instance

/-- `b1`'s exit: `read_scalar`'s tag not `1`. -/
def c1 : SBool := .not (.cmp .eq .W32 (.load 0 128 4) (.lit 1))
/-- `b3`'s, `b5`'s exit: the tag `0`. -/
def c3 : SBool := .cmp .eq .W8 (.load 0 128 1) (.lit 0)
/-- `b7`'s exit: `eq_kernel` failed. -/
def c7 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.lit 1)) (.lit 0)
/-- `b10`'s exit: limb `0` differs. -/
def c10 : SBool := .not (.cmp .eq .W64 (.load 0 104 8) (.reg .rax))
/-- `b11`'s exit: limb `1` differs. -/
def c11 : SBool := .not (.cmp .eq .W64 (.load 0 96 8) (.reg .rdx))
/-- `b12`'s exit: `bytecode_low` empty. -/
def c12 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .rbp) (.reg .rbp)) (.lit 0)
/-- `b13`'s exit: more than one element. -/
def c13 : SBool := .not (.cmp .eq .W64 (.reg .rbp) (.lit 1))
/-- `b18`'s exit: more pairs. -/
def c18 : SBool := .not (.cmp .eq .W64 (.reg .rsi) (.bin .add .W64 (.lit 2) (.reg .rdx)))
/-- `b19`'s exit: an even length. -/
def c19 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rbp) (.lit 1)) (.lit 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 bodyS
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 bodyS
sym_block run_b4 := exec b4 bodyS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 bodyS
sym_block run_b9 := exec b9 bodyS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 bodyS
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 bodyS
sym_block run_b14 := exec b14 bodyS
sym_block run_b15 := exec b15 outS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 bodyS
sym_block run_b18 := exec b18 pairS
sym_block run_b19 := exec b19 bodyS
sym_block run_b20 := exec b20 oneS
sym_block run_b21 := exec b21 endS

/-! ## The calls -/

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 432 0 slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 128) ∧
    (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) ∧
    (after b0 entryS).reg .rbp = some (.reg .r8) ∧
    (after b0 entryS).reg .r12 = some (.reg .r9) ∧
    (after b0 entryS).reg .r13 = some (.reg .rcx) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdx) ∧
    (after b0 entryS).reg .r15 = some (.reg .rsi) ∧
    WritesF (after b0 entryS) 384 432 := by
  decide +kernel

public theorem exit_b2 : exec b2 bodyS = some (after b2 bodyS,
    .call NativeRustcVmX64.Vm.SumcheckOfSumcheckPlain.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : MidOk 432 0 slots (after b2 bodyS) = true ∧
    (after b2 bodyS).reg .rdi = some (.ptr 0 128) ∧
    (after b2 bodyS).reg .rsi = some (.reg .r15) ∧
    (after b2 bodyS).reg .rdx = some (.load 0 136 8) ∧
    (after b2 bodyS).reg .rcx = some (.load 0 144 8) ∧
    (after b2 bodyS).reg .r8 = some (.lit 3) ∧
    (after b2 bodyS).reg .r9 = some (.ptr 0 32) ∧
    KeepsB (after b2 bodyS) six = true ∧
    WordW 0 8 (.lit 4) (after b2 bodyS) ∧
    WordW 0 112 (.load 0 144 8) (after b2 bodyS) ∧
    WordW 0 120 (.load 0 136 8) (after b2 bodyS) ∧
    (∀ w ∈ (after b2 bodyS).mem, w.r = 0 ∧
      (w.off + w.n ≤ 96 ∨ 112 ≤ w.off ∧ w.off + w.n ≤ 128)) := by
  decide +kernel

public theorem exit_b4 : exec b4 bodyS = some (after b4 bodyS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 432 0 slots (after b4 bodyS) = true ∧
    (after b4 bodyS).reg .rdi = some (.ptr 0 128) ∧
    (after b4 bodyS).reg .rsi = some (.reg .r15) ∧
    KeepsB (after b4 bodyS) six = true ∧
    WordW 0 96 (.load 0 144 8) (after b4 bodyS) ∧
    WordW 0 104 (.load 0 136 8) (after b4 bodyS) ∧
    WritesF (after b4 bodyS) 96 112 := by
  decide +kernel

public theorem exit_b6 : exec b6 bodyS = some (after b6 bodyS,
    .call NativeRustcVmX64.Vm.EqKernel.entryLabel) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : MidOk 432 0 slots (after b6 bodyS) = true ∧
    (after b6 bodyS).reg .rdi = some (.ptr 0 32) ∧
    (after b6 bodyS).reg .rsi = some (.lit 4) ∧
    (after b6 bodyS).reg .rdx = some (.ptr 0 128) ∧
    (after b6 bodyS).reg .rcx = some (.lit 16) ∧
    (after b6 bodyS).reg .r15 = some (.load 0 136 8) ∧
    KeepsB (after b6 bodyS) [.rbx, .rbp, .r12, .r13, .r14] = true ∧
    WordW 0 24 (.load 0 144 8) (after b6 bodyS) ∧
    (∀ w ∈ (after b6 bodyS).mem, w.r = 0 ∧
      (w.off + w.n ≤ 8 ∨ 24 ≤ w.off ∧ w.off + w.n ≤ 32 ∨ 128 ≤ w.off ∧ w.off + w.n ≤ 384)) := by
  decide +kernel

public theorem exit_b8 : exec b8 bodyS = some (after b8 bodyS,
    .call NativeRustcVmX64.Vm.Dot.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : MidOk 432 0 slots (after b8 bodyS) = true ∧
    (after b8 bodyS).reg .rdi = some (.ptr 0 128) ∧
    (after b8 bodyS).reg .rsi = some (.lit 16) ∧
    (after b8 bodyS).reg .rdx = some (.reg .r14) ∧
    (after b8 bodyS).reg .rcx = some (.lit 16) ∧
    KeepsB (after b8 bodyS) six = true ∧ WritesF (after b8 bodyS) 8 8 := by
  decide +kernel

public theorem exit_b9 : exec b9 bodyS = some (after b9 bodyS,
    .call NativeRustcVmX64.Vm.EWMul.entryLabel) :=
  run_b9.trans (by rw [after_eq run_b9])
public theorem ok_b9 : MidOk 432 0 slots (after b9 bodyS) = true ∧
    (after b9 bodyS).reg .rdi = some (.reg .rax) ∧
    (after b9 bodyS).reg .rsi = some (.reg .rdx) ∧
    (after b9 bodyS).reg .rdx = some (.reg .r15) ∧
    (after b9 bodyS).reg .rcx = some (.load 0 24 8) ∧
    KeepsB (after b9 bodyS) six = true ∧ WritesF (after b9 bodyS) 8 8 := by
  decide +kernel

/-! ## The tests -/

public theorem exit_b1 : exec b1 bodyS = some (after b1 bodyS, .cond c1 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem exit_b3 : exec b3 bodyS = some (after b3 bodyS, .cond c3 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem exit_b5 : exec b5 bodyS = some (after b5 bodyS, .cond c3 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b5.trans (by rw [after_eq run_b5]; rfl)
public theorem exit_b7 : exec b7 bodyS = some (after b7 bodyS, .cond c7 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b7.trans (by rw [after_eq run_b7]; rfl)
public theorem exit_b10 : exec b10 bodyS = some (after b10 bodyS, .cond c10 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem exit_b11 : exec b11 bodyS = some (after b11 bodyS, .cond c11 NativeRustcVmX64.Vm.BytecodeShare.label_14) :=
  run_b11.trans (by rw [after_eq run_b11]; rfl)
public theorem ok_test : MidOk 432 8 slots (after b1 bodyS) = true ∧ (after b1 bodyS).mem = [] ∧
    KeepsB (after b1 bodyS) six = true ∧
    MidOk 432 8 slots (after b3 bodyS) = true ∧ (after b3 bodyS).mem = [] ∧
    KeepsB (after b3 bodyS) six = true ∧
    MidOk 432 8 slots (after b5 bodyS) = true ∧ (after b5 bodyS).mem = [] ∧
    KeepsB (after b5 bodyS) six = true ∧
    MidOk 432 8 slots (after b7 bodyS) = true ∧ (after b7 bodyS).mem = [] ∧
    KeepsB (after b7 bodyS) six = true ∧
    MidOk 432 8 slots (after b10 bodyS) = true ∧ (after b10 bodyS).mem = [] ∧
    KeepsB (after b10 bodyS) (.rdx :: six) = true ∧
    MidOk 432 8 slots (after b11 bodyS) = true ∧ (after b11 bodyS).mem = [] ∧
    KeepsB (after b11 bodyS) six = true := by
  decide +kernel

/-! ## The copy -/

public theorem exit_b12 : exec b12 bodyS = some (after b12 bodyS, .cond c12 NativeRustcVmX64.Vm.BytecodeShare.label_11) :=
  run_b12.trans (by rw [after_eq run_b12]; rfl)
public theorem ok_b12 : MidOk 432 8 slots (after b12 bodyS) = true ∧ (after b12 bodyS).mem = [] ∧
    KeepsB (after b12 bodyS) six = true ∧
    (after b12 bodyS).reg .rax = some (.bin .add .W64 (.reg .rbp) (.lit 4)) ∧
    (after b12 bodyS).reg .rcx =
      some (.bin .add .W64 (.reg .r12) (.bin .shl .W64 (.reg .rbp) (.lit 4))) := by
  decide +kernel

public theorem exit_b13 : exec b13 bodyS = some (after b13 bodyS, .cond c13 NativeRustcVmX64.Vm.BytecodeShare.label_12) :=
  run_b13.trans (by rw [after_eq run_b13]; rfl)
public theorem exit_b14 : exec b14 bodyS = some (after b14 bodyS, .jump NativeRustcVmX64.Vm.BytecodeShare.label_10) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem exit_b17 : exec b17 bodyS = some (after b17 bodyS, .fall) :=
  run_b17.trans (by rw [after_eq run_b17])
public theorem exit_b19 : exec b19 bodyS = some (after b19 bodyS, .cond c19 NativeRustcVmX64.Vm.BytecodeShare.label_11) :=
  run_b19.trans (by rw [after_eq run_b19]; rfl)
public theorem ok_moves : MidOk 432 8 slots (after b13 bodyS) = true ∧ (after b13 bodyS).mem = [] ∧
    KeepsB (after b13 bodyS) (.rax :: .rcx :: six) = true ∧
    MidOk 432 8 slots (after b14 bodyS) = true ∧ (after b14 bodyS).mem = [] ∧
    KeepsB (after b14 bodyS) (.rax :: .rcx :: six) = true ∧
    (after b14 bodyS).reg .rdx = some (.lit 0) ∧
    MidOk 432 8 slots (after b17 bodyS) = true ∧ (after b17 bodyS).mem = [] ∧
    KeepsB (after b17 bodyS) (.rax :: .rcx :: six) = true ∧
    (after b17 bodyS).reg .rdx = some (.lit 0) ∧ (after b17 bodyS).reg .rdi = some (.lit 24) ∧
    (after b17 bodyS).reg .rsi =
      some (.bin .and .W32 (.un .trunc .W32 (.reg .rbp)) (.lit 62)) ∧
    MidOk 432 8 slots (after b19 bodyS) = true ∧ (after b19 bodyS).mem = [] ∧
    KeepsB (after b19 bodyS) (.rax :: .rcx :: .rdx :: six) = true := by
  decide +kernel

public theorem exit_b18 : exec b18 pairS = some (after b18 pairS, .cond c18 NativeRustcVmX64.Vm.BytecodeShare.label_13) :=
  run_b18.trans (by rw [after_eq run_b18]; rfl)
public theorem ok_b18 : MidOk 432 8 slots (after b18 pairS) = true ∧
    KeepsB (after b18 pairS) (.rax :: .rcx :: .rsi :: six) = true ∧
    (after b18 pairS).reg .rdx = some (.bin .add .W64 (.lit 2) (.reg .rdx)) ∧
    (after b18 pairS).reg .rdi = some (.bin .add .W64 (.lit 32) (.reg .rdi)) ∧
    CopyW (after b18 pairS) 2 0 1 0 4 ∧
    (∀ w ∈ (after b18 pairS).mem, w.r = 2 ∧ w.off + w.n ≤ 32) := by
  decide +kernel

public theorem exit_b20 : exec b20 oneS = some (after b20 oneS, .fall) :=
  run_b20.trans (by rw [after_eq run_b20])
public theorem ok_b20 : MidOk 432 8 slots (after b20 oneS) = true ∧
    KeepsB (after b20 oneS) (.rax :: .rcx :: six) = true ∧
    CopyW (after b20 oneS) 2 0 1 0 2 ∧
    (∀ w ∈ (after b20 oneS).mem, w.r = 2 ∧ w.off + w.n ≤ 16) := by
  decide +kernel

public theorem exit_b21 : exec b21 endS = some (after b21 endS, .jump NativeRustcVmX64.Vm.BytecodeShare.label_15) :=
  run_b21.trans (by rw [after_eq run_b21])
public theorem ok_b21 : MidOk 432 8 slots (after b21 endS) = true ∧
    KeepsB (after b21 endS) [.rbp, .r12, .r13, .r14, .r15] = true ∧
    (after b21 endS).reg .rbx = some (.ptr 1 0) ∧
    WordW 1 0 (.lit 1) (after b21 endS) ∧ WordW 1 8 (.load 0 120 8) (after b21 endS) ∧
    WordW 1 16 (.load 0 112 8) (after b21 endS) ∧ WordW 1 24 (.reg .rax) (after b21 endS) ∧
    WordW 1 32 (.reg .r15) (after b21 endS) ∧ WordW 1 40 (.load 0 24 8) (after b21 endS) ∧
    CopyW (after b21 endS) 2 0 0 32 8 ∧
    (∀ w ∈ (after b21 endS).mem, w.r = 1 ∧ w.off + w.n ≤ 48 ∨ w.r = 2 ∧ w.off + w.n ≤ 64) := by
  decide +kernel

/-! ## The exits -/

public theorem exit_b15 : exec b15 outS = some (after b15 outS, .fall) :=
  run_b15.trans (by rw [after_eq run_b15])
public theorem ok_b15 : MidOk 432 8 slots (after b15 outS) = true ∧
    KeepsB (after b15 outS) [.rbp, .r12, .r13, .r14, .r15] = true ∧
    (after b15 outS).reg .rbx = some (.ptr 1 0) ∧ WordW 1 0 (.lit 0) (after b15 outS) ∧
    (∀ w ∈ (after b15 outS).mem, w.r = 1 ∧ w.off + w.n ≤ 8) := by
  decide +kernel

public theorem exit_b16 : exec b16 bodyS = some (after b16 bodyS, .ret (.load 0 432 8)) :=
  run_b16.trans (by rw [after_eq run_b16])
public theorem ok_b16 : EpiOk 432 slots (after b16 bodyS) = true ∧ (after b16 bodyS).mem = [] := by
  decide +kernel

end NativeRustcVmX64.Bus.BytecodeShare
