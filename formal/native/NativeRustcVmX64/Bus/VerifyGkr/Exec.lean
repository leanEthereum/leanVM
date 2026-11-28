module

public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts.Names
public meta import NativeRustcVmX64.Code.Vm.VerifyGkrGrandProducts
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `verify_gkr_grand_products`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 80-byte frame below the entry's RSP and the return address (`Frame`, `F = 80`):
RBP to RBX pushed at offsets `72` to `32`, `read_scalar`'s `Option<EW>` at `8`, RSP at offset `8`
in the body, a callee's return address at `0`. `entryS` at the entry (`b0`: the prologue, the
first `read_scalar(frame + 8, t)`); `headS` for `b1` to `b3` and `b5` (the tags, the second
`read_scalar`); `sS` for `b4` (region 1 the `GkrStateW` at R14: its values and the point's length
set, `gkr_layers(t, depth, s)`); `oS` for the ends (region 1 the output at RBX): `b6` (the root),
then `b8` (the tag `1`, the epilogue), or `b7` then `b8` (the tag `0`).
-/

namespace NativeRustcVmX64.Bus.VerifyGkr

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyGkrGrandProducts
open NativeRustcVmX64.Transcript NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .rbp), (64, .r15), (56, .r14), (48, .r13), (40, .r12), (32, .rbx)]

/-- At the entry. -/
def entryS : SState := init [88] [(.rsp, .ptr 0 80)]
/-- In the body. -/
def headS : SState := init [88] [(.rsp, .ptr 0 8)]
/-- In the body, the `GkrStateW` region 1 (R14). -/
def sS : SState := init [88, 1064] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]
/-- In the body, the output region 1 (RBX). -/
def oS : SState := init [88, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- The callee-saved registers a block keeps. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- An end: the epilogue, RAX the tag `v`, the tag word written at the output. -/
def EndOk (S : SState) (v : Nat) : Bool :=
  EpiOk 80 slots S && S.reg .rax == some (.lit v) &&
    S.mem.all (fun w ↦ w.r == 1 && decide (w.off + w.n ≤ 24))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 headS
sym_block run_b2 := exec b2 headS
sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 sS
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 oS
sym_block run_b8s := exec b8 (after b6 oS)
sym_block run_b7 := exec b7 oS
sym_block run_b8f := exec b8 (after b7 oS)

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 80 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 32 ≤ w.off)) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 8) ∧ (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdi) ∧ (after b0 entryS).reg .r12 = some (.reg .rsi) ∧
    (after b0 entryS).reg .r14 = some (.reg .rcx) ∧ (after b0 entryS).reg .r15 = some (.reg .rdx) := by
  decide +kernel

public theorem exit_b1 : exec b1 headS = some (after b1 headS,
    .cond (SBool.cmp .eq .W32 (.load 0 8 4) (.lit 1)).not NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : MidOk 80 8 slots (after b1 headS) = true ∧ (after b1 headS).mem = [] ∧
    Keeps (after b1 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b2 : exec b2 headS = some (after b2 headS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : MidOk 80 0 slots (after b2 headS) = true ∧
    (∀ w ∈ (after b2 headS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 headS).reg .rdi = some (.ptr 0 8) ∧ (after b2 headS).reg .rsi = some (.reg .r12) ∧
    (after b2 headS).reg .r13 = some (.load 0 16 8) ∧ (after b2 headS).reg .rbp = some (.load 0 24 8) ∧
    Keeps (after b2 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b3 : exec b3 headS = some (after b3 headS,
    .cond (.cmp .eq .W8 (.load 0 8 1) (.lit 0)) NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 80 8 slots (after b3 headS) = true ∧ (after b3 headS).mem = [] ∧
    Keeps (after b3 headS) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b4 : exec b4 sS = some (after b4 sS,
    .call NativeRustcVmX64.Vm.GkrLayers.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 80 0 slots (after b4 sS) = true ∧
    (∀ w ∈ (after b4 sS).mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 56)) ∧
    WordW 1 0 (.reg .r13) (after b4 sS) ∧ WordW 1 8 (.reg .rbp) (after b4 sS) ∧
    WordW 1 16 (.reg .r13) (after b4 sS) ∧ WordW 1 24 (.reg .rbp) (after b4 sS) ∧
    WordW 1 32 (.load 0 16 8) (after b4 sS) ∧ WordW 1 40 (.load 0 24 8) (after b4 sS) ∧
    WordW 1 48 (.lit 0) (after b4 sS) ∧
    (after b4 sS).reg .rdi = some (.reg .r12) ∧ (after b4 sS).reg .rsi = some (.reg .r15) ∧
    (after b4 sS).reg .rdx = some (.ptr 1 0) ∧ (after b4 sS).reg .r13 = some (.load 0 16 8) ∧
    (after b4 sS).reg .rbp = some (.load 0 24 8) ∧ (after b4 sS).reg .r14 = some (.ptr 1 0) ∧
    Keeps (after b4 sS) [.rbx, .r12, .r15] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 headS = some (after b5 headS,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0))
      NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_5) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : MidOk 80 8 slots (after b5 headS) = true ∧ (after b5 headS).mem = [] ∧
    Keeps (after b5 headS) [.rbx, .rbp, .r12, .r13, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b6 : exec b6 oS = some (after b6 oS, .jump NativeRustcVmX64.Vm.VerifyGkrGrandProducts.label_6) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem exit_b8s : exec b8 (after b6 oS) = some (after b8 (after b6 oS), .ret (.load 0 80 8)) :=
  run_b8s.trans (by rw [after_eq run_b8s])
public theorem ok_b8s : EndOk (after b8 (after b6 oS)) 1 = true ∧
    WordW 1 0 (.lit 1) (after b8 (after b6 oS)) ∧ WordW 1 8 (.reg .r13) (after b8 (after b6 oS)) ∧
    WordW 1 16 (.reg .rbp) (after b8 (after b6 oS)) := by
  decide +kernel

public theorem exit_b7 : exec b7 oS = some (after b7 oS, .fall) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem exit_b8f : exec b8 (after b7 oS) = some (after b8 (after b7 oS), .ret (.load 0 80 8)) :=
  run_b8f.trans (by rw [after_eq run_b8f])
public theorem ok_b8f : EndOk (after b8 (after b7 oS)) 0 = true ∧
    WordW 1 0 (.lit 0) (after b8 (after b7 oS)) := by
  decide +kernel

end NativeRustcVmX64.Bus.VerifyGkr
