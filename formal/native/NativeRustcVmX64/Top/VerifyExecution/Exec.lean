module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.VerifyExecution
public meta import NativeRustcVmX64.Code.Vm.VerifyExecution
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `verify_execution`'s blocks, run by the symbolic executor (x86-64)

Region 0 the frame: the 96 bytes below the entry's RSP and the return address (RBP, R15, R14, R13,
R12, RBX pushed at offsets `88` to `48`, `pushq %rax`'s slot at `40` holding the public input's,
later the Keccak output's address; RSP at offset `40` between the calls, a callee's return address
at `32`, `verify_stacked_opening`'s three argument words at `8` to `31` below its return address at
`0`). `entryS` at the entry (`b0`); `bodyS` between the calls; `workS` with region 1 the working
area's first 72 bytes at RBX, for `b2` and `b14`, which read the layout; `retS` after
`verify_stacked_opening` (`b19`); `exitS` at the epilogue (`b21`).
-/

namespace NativeRustcVmX64.Top.VerifyExecution

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.VerifyExecution NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(88, .rbp), (80, .r15), (72, .r14), (64, .r13), (56, .r12), (48, .rbx)]

def entryS : SState := init [104] [(.rsp, .ptr 0 96)]
def bodyS : SState := init [104] [(.rsp, .ptr 0 40)]
def workS : SState := init [104, 72] [(.rsp, .ptr 0 40), (.rbx, .ptr 1 0)]
def retS : SState := init [104] [(.rsp, .ptr 0 8)]
def exitS : SState := init [104] [(.rsp, .ptr 0 48)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 bodyS
sym_block run_b2 := exec b2 workS
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
sym_block run_b14 := exec b14 workS
sym_block run_b15 := exec b15 bodyS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 bodyS
sym_block run_b18 := exec b18 bodyS
sym_block run_b19 := exec b19 retS
sym_block run_b20 := exec b20 bodyS
sym_block run_b21 := exec b21 exitS

/-- The prologue: the slots, the public input at offset `40`, `read_announced_sizes`'s
arguments. -/
public theorem ok_b0 : ProOk 96 32 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 32 ≤ w.off ∧ w.off + w.n ≤ 96) ∧
    (∀ j < 8, findWrite 0 (40 + j) (after b0 entryS).mem = some (.reg .rcx, j)) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) ∧ (after b0 entryS).reg .rsi = some (.reg .rdx) ∧
    (after b0 entryS).reg .rdx = some (.reg .r8) ∧ (after b0 entryS).reg .rbx = some (.reg .r8) ∧
    (after b0 entryS).reg .r12 = some (.reg .rsi) ∧ (after b0 entryS).reg .r13 = some (.reg .rdx) ∧
    (after b0 entryS).reg .r14 = some (.reg .rdi) := by
  decide +kernel

/-- `b1`: `read_announced_sizes`'s tag tested. -/
public theorem ok_b1 : MidOk 96 40 slots (after b1 bodyS) = true ∧ (after b1 bodyS).mem = [] ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b1 bodyS).reg r == some (.reg r)) = true ∧ (after b1 bodyS).reg .rdx = some (.reg .rdx) := by
  decide +kernel

/-- A test of AL. -/
public theorem ok_test : ∀ b ∈ [b3, b5, b7, b9, b11, b13, b15, b17],
    MidOk 96 40 slots (after b bodyS) = true ∧ (after b bodyS).mem = [] ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b2`: the rate to R15, the stack's log-size from the layout to RBP, `commit_stack`. -/
public theorem ok_b2 : MidOk 96 32 slots (after b2 workS) = true ∧
    (∀ w ∈ (after b2 workS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b2 workS).reg .rdi = some (.reg .r14) ∧ (after b2 workS).reg .rsi = some (.load 1 16 8) ∧
    (after b2 workS).reg .rdx = some (.reg .rdx) ∧ (after b2 workS).reg .r15 = some (.reg .rdx) ∧
    (after b2 workS).reg .rbp = some (.load 1 16 8) ∧ (after b2 workS).reg .rbx = some (.ptr 1 0) ∧
    [Reg64.r12, .r13, .r14].all (fun r ↦ (after b2 workS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b4`: `read_ood` into the working area's bytes from `3912`, kept in RBP. -/
public theorem ok_b4 : MidOk 96 32 slots (after b4 bodyS) = true ∧
    (∀ w ∈ (after b4 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b4 bodyS).reg .rdi = some (.reg .r14) ∧ (after b4 bodyS).reg .rsi = some (.reg .rbp) ∧
    (after b4 bodyS).reg .rdx = some (.bin .add .W64 (.reg .rbx) (.lit 3912)) ∧
    (after b4 bodyS).reg .rbp = some (.bin .add .W64 (.reg .rbx) (.lit 3912)) ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15].all (fun r ↦ (after b4 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b6`: `verify_bus_balance`, the bus and the claims kept in R12, R13. -/
public theorem ok_b6 : MidOk 96 32 slots (after b6 bodyS) = true ∧
    (∀ w ∈ (after b6 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b6 bodyS).reg .rdi = some (.reg .r14) ∧ (after b6 bodyS).reg .rsi = some (.reg .rbx) ∧
    (after b6 bodyS).reg .rdx = some (.reg .r12) ∧ (after b6 bodyS).reg .rcx = some (.reg .r13) ∧
    (after b6 bodyS).reg .r8 = some (.bin .add .W64 (.reg .rbx) (.lit 4416)) ∧
    (after b6 bodyS).reg .r9 = some (.bin .add .W64 (.reg .rbx) (.lit 123992)) ∧
    (after b6 bodyS).reg .r12 = some (.bin .add .W64 (.reg .rbx) (.lit 4416)) ∧
    (after b6 bodyS).reg .r13 = some (.bin .add .W64 (.reg .rbx) (.lit 123992)) ∧
    [Reg64.rbx, .r14, .r15, .rbp].all (fun r ↦ (after b6 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b8`: `table_phase`, the evaluations kept in R12. -/
public theorem ok_b8 : MidOk 96 32 slots (after b8 bodyS) = true ∧
    (∀ w ∈ (after b8 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b8 bodyS).reg .rdi = some (.reg .r14) ∧ (after b8 bodyS).reg .rsi = some (.reg .rbx) ∧
    (after b8 bodyS).reg .rdx = some (.reg .r12) ∧
    (after b8 bodyS).reg .rcx = some (.bin .add .W64 (.reg .rbx) (.lit 112184)) ∧
    (after b8 bodyS).reg .r12 = some (.bin .add .W64 (.reg .rbx) (.lit 112184)) ∧
    [Reg64.rbx, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b8 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b10`: `table_column_claims`. -/
public theorem ok_b10 : MidOk 96 32 slots (after b10 bodyS) = true ∧
    (∀ w ∈ (after b10 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b10 bodyS).reg .rdi = some (.reg .r12) ∧ (after b10 bodyS).reg .rsi = some (.reg .r13) ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b10 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b12`: `public_input_phase`, the public input read back from offset `40`. -/
public theorem ok_b12 : MidOk 96 32 slots (after b12 bodyS) = true ∧
    (∀ w ∈ (after b12 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b12 bodyS).reg .rdi = some (.reg .r14) ∧ (after b12 bodyS).reg .rsi = some (.reg .rbx) ∧
    (after b12 bodyS).reg .rdx = some (.load 0 40 8) ∧ (after b12 bodyS).reg .rcx = some (.reg .r13) ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b12 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b14`: `keccak_phase`, the Keccak output's address stored at offset `40`. -/
public theorem ok_b14 : MidOk 96 32 slots (after b14 workS) = true ∧
    (∀ w ∈ (after b14 workS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (∀ j < 8, findWrite 0 (40 + j) (after b14 workS).mem = some (.ptr 1 221280, j)) ∧
    (after b14 workS).reg .rdi = some (.reg .r14) ∧ (after b14 workS).reg .rsi = some (.load 1 64 8) ∧
    (after b14 workS).reg .rdx = some (.reg .r12) ∧
    (after b14 workS).reg .rcx = some (.ptr 1 289728) ∧
    (after b14 workS).reg .r8 = some (.reg .r13) ∧ (after b14 workS).reg .r9 = some (.ptr 1 221280) ∧
    (after b14 workS).reg .rbx = some (.ptr 1 0) ∧
    [Reg64.r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b14 workS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b16`: `ring_switch`, its output kept in R12. -/
public theorem ok_b16 : MidOk 96 32 slots (after b16 bodyS) = true ∧
    (∀ w ∈ (after b16 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (after b16 bodyS).reg .rdi = some (.reg .r14) ∧
    (after b16 bodyS).reg .rsi = some (.bin .add .W64 (.reg .rbx) (.lit 221864)) ∧
    (after b16 bodyS).reg .rdx = some (.bin .add .W64 (.reg .rbx) (.lit 222888)) ∧
    (after b16 bodyS).reg .r12 = some (.bin .add .W64 (.reg .rbx) (.lit 222888)) ∧
    [Reg64.rbx, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b16 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b18`: `verify_stacked_opening`, its three argument words at offsets `8` to `31`. -/
public theorem ok_b18 : MidOk 96 0 slots (after b18 bodyS) = true ∧
    (∀ w ∈ (after b18 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (∀ j < 8, findWrite 0 (8 + j) (after b18 bodyS).mem = some (.reg .rbp, j)) ∧
    (∀ j < 8, findWrite 0 (16 + j) (after b18 bodyS).mem =
      some (.bin .add .W64 (.reg .rbx) (.lit 223928), j)) ∧
    (∀ j < 8, findWrite 0 (24 + j) (after b18 bodyS).mem =
      some (.bin .add .W64 (.reg .rbx) (.lit 226528), j)) ∧
    (after b18 bodyS).reg .rdi = some (.reg .r14) ∧ (after b18 bodyS).reg .rsi = some (.reg .rbx) ∧
    (after b18 bodyS).reg .rdx = some (.reg .r15) ∧ (after b18 bodyS).reg .rcx = some (.reg .r12) ∧
    (after b18 bodyS).reg .r8 = some (.load 0 40 8) ∧ (after b18 bodyS).reg .r9 = some (.reg .r13) ∧
    [Reg64.rbx, .r12, .r13, .r14, .r15, .rbp].all (fun r ↦ (after b18 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b19`: the stack arguments dropped, AL kept. -/
public theorem ok_b19 : MidOk 96 48 slots (after b19 retS) = true ∧ (after b19 retS).mem = [] ∧
    (after b19 retS).reg .rax = some (.reg .rax) := by
  decide +kernel

/-- `b20`: `0`. -/
public theorem ok_b20 : MidOk 96 48 slots (after b20 bodyS) = true ∧ (after b20 bodyS).mem = [] ∧
    (after b20 bodyS).reg .rax = some (.lit 0) := by
  decide +kernel

/-- `b21`: the epilogue, RAX kept. -/
public theorem ok_b21 : EpiOk 96 slots (after b21 exitS) = true ∧ (after b21 exitS).mem = [] ∧
    (after b21 exitS).reg .rax = some (.reg .rax) := by
  decide +kernel

end NativeRustcVmX64.Top.VerifyExecution
