module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.LeanvmVerify
public meta import NativeRustcVmX64.Code.Vm.LeanvmVerify
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `leanvm_verify`'s blocks, run by the symbolic executor (x86-64)

Region 0 the frame: the 112 bytes below the entry's RSP and the return address (RBP, R15, R14,
R13, R12, RBX pushed at offsets `104` to `64`; RSP at offset `8` in the body, the public input at
offsets `8` to `39`, the `Decoded` at `40` to `63`, a callee's return address at `0`). `entryS` at
the entry, region 1 the context's first 96 bytes at RDI (`b0`: the prologue, `L`); `ctxS` at `b1`
to `b6` (the counts' and the areas' checks, the addresses and the public input read); `bodyS`
elsewhere (`b7` to `b9`: the bytecode's and the wire's checks; `b10`, `b14`: `decode`; `b11`,
`b15`: its verdict; `b16`: `verify`; `b17`: its verdict; `b12`: `0`; `b13`: the epilogue).
-/

namespace NativeRustcVmX64.Top.Leanvm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.LeanvmVerify NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(104, .rbp), (96, .r15), (88, .r14), (80, .r13), (72, .r12), (64, .rbx)]

def entryS : SState := init [120, 96] [(.rsp, .ptr 0 112), (.rdi, .ptr 1 0)]
def ctxS : SState := init [120, 96] [(.rsp, .ptr 0 8), (.rdi, .ptr 1 0)]
def bodyS : SState := init [120] [(.rsp, .ptr 0 8)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 ctxS
sym_block run_b2 := exec b2 ctxS
sym_block run_b3 := exec b3 ctxS
sym_block run_b4 := exec b4 ctxS
sym_block run_b5 := exec b5 ctxS
sym_block run_b6 := exec b6 ctxS
sym_block run_b7 := exec b7 bodyS
sym_block run_b8 := exec b8 bodyS
sym_block run_b9 := exec b9 bodyS
sym_block run_b10 := exec b10 bodyS
sym_block run_b11 := exec b11 bodyS
sym_block run_b12 := exec b12 bodyS
sym_block run_b13 := exec b13 bodyS
sym_block run_b14 := exec b14 bodyS
sym_block run_b15 := exec b15 bodyS
sym_block run_b16 := exec b16 bodyS
sym_block run_b17 := exec b17 bodyS

public theorem ok_b0 : ProOk 112 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    (after b0 entryS).reg .rbx = some (.load 1 8 8) ∧
    (after b0 entryS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel

/-- The checks' blocks: no write, the frame's slots and RSP kept, the registers they set. -/
public theorem ok_b1 : MidOk 112 8 slots (after b1 ctxS) = true ∧ (after b1 ctxS).mem = [] ∧
    (after b1 ctxS).reg .r14 = some (.load 1 24 8) ∧ (after b1 ctxS).reg .rbx = some (.reg .rbx) ∧
    (after b1 ctxS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b2 : MidOk 112 8 slots (after b2 ctxS) = true ∧ (after b2 ctxS).mem = [] ∧
    (after b2 ctxS).reg .r15 = some (.bin .add .W64 (.lit 395289)
      (.bin .or .W64 (.bin .shr .W64 (.reg .rbx) (.lit 3)) (.lit 1))) ∧
    (after b2 ctxS).reg .rbx = some (.reg .rbx) ∧ (after b2 ctxS).reg .r14 = some (.reg .r14) ∧
    (after b2 ctxS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b3 : MidOk 112 8 slots (after b3 ctxS) = true ∧ (after b3 ctxS).mem = [] ∧
    (after b3 ctxS).reg .rbx = some (.reg .rbx) ∧ (after b3 ctxS).reg .r14 = some (.reg .r14) ∧
    (after b3 ctxS).reg .r15 = some (.reg .r15) ∧ (after b3 ctxS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b4 : MidOk 112 8 slots (after b4 ctxS) = true ∧ (after b4 ctxS).mem = [] ∧
    (after b4 ctxS).reg .r12 = some (.load 1 64 8) ∧
    (after b4 ctxS).reg .rbx = some (.reg .rbx) ∧ (after b4 ctxS).reg .r14 = some (.reg .r14) ∧
    (after b4 ctxS).reg .r15 = some (.reg .r15) ∧ (after b4 ctxS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b5 : MidOk 112 8 slots (after b5 ctxS) = true ∧ (after b5 ctxS).mem = [] ∧
    (after b5 ctxS).reg .r13 = some (.load 1 80 8) ∧ (after b5 ctxS).reg .r12 = some (.reg .r12) ∧
    (after b5 ctxS).reg .rbx = some (.reg .rbx) ∧ (after b5 ctxS).reg .r14 = some (.reg .r14) ∧
    (after b5 ctxS).reg .r15 = some (.reg .r15) ∧ (after b5 ctxS).reg .rdi = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b6 : MidOk 112 8 slots (after b6 ctxS) = true ∧ (after b6 ctxS).mem = [] ∧
    (after b6 ctxS).reg .rax = some (.load 1 0 8) ∧ (after b6 ctxS).reg .rbp = some (.load 1 16 8) ∧
    (after b6 ctxS).reg .r8 = some (.load 1 32 8) ∧ (after b6 ctxS).reg .rsi = some (.load 1 40 8) ∧
    (after b6 ctxS).reg .rdx = some (.load 1 48 8) ∧ (after b6 ctxS).reg .rcx = some (.load 1 56 8) ∧
    (after b6 ctxS).reg .r12 = some (.reg .r12) ∧ (after b6 ctxS).reg .r13 = some (.reg .r13) ∧
    (after b6 ctxS).reg .rbx = some (.reg .rbx) ∧ (after b6 ctxS).reg .r14 = some (.reg .r14) ∧
    (after b6 ctxS).reg .r15 = some (.reg .r15) := by
  decide +kernel

public theorem ok_b7 : MidOk 112 8 slots (after b7 bodyS) = true ∧ (after b7 bodyS).mem = [] ∧
    [Reg64.rax, .rbp, .r8, .rsi, .rdx, .rcx, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b7 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel
public theorem ok_b8 : MidOk 112 8 slots (after b8 bodyS) = true ∧ (after b8 bodyS).mem = [] ∧
    [Reg64.rax, .rbp, .r8, .rsi, .rdx, .rcx, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b8 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel
public theorem ok_b9 : MidOk 112 8 slots (after b9 bodyS) = true ∧ (after b9 bodyS).mem = [] ∧
    [Reg64.rax, .rbp, .r8, .rsi, .rdx, .rcx, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b9 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b10`, `b14`: the public input to the frame's bytes 8 to 39, `decode`'s arguments. -/
public theorem ok_b10 : MidOk 112 0 slots (after b10 bodyS) = true ∧
    (∀ w ∈ (after b10 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (∀ j < 8, findWrite 0 (8 + j) (after b10 bodyS).mem = some (.reg .r8, j)) ∧
    (∀ j < 8, findWrite 0 (16 + j) (after b10 bodyS).mem = some (.reg .rsi, j)) ∧
    (∀ j < 8, findWrite 0 (24 + j) (after b10 bodyS).mem = some (.reg .rdx, j)) ∧
    (∀ j < 8, findWrite 0 (32 + j) (after b10 bodyS).mem = some (.reg .rcx, j)) ∧
    (after b10 bodyS).reg .rdi = some (.reg .rax) ∧ (after b10 bodyS).reg .rsi = some (.reg .rbx) ∧
    (after b10 bodyS).reg .rdx = some (.reg .r12) ∧ (after b10 bodyS).reg .rcx = some (.reg .r15) ∧
    (after b10 bodyS).reg .r8 = some (.reg .r13) ∧
    [Reg64.rbp, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b10 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel
public theorem ok_b14 : MidOk 112 0 slots (after b14 bodyS) = true ∧
    (∀ w ∈ (after b14 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 40) ∧
    (∀ j < 8, findWrite 0 (8 + j) (after b14 bodyS).mem = some (.reg .r8, j)) ∧
    (∀ j < 8, findWrite 0 (16 + j) (after b14 bodyS).mem = some (.reg .rsi, j)) ∧
    (∀ j < 8, findWrite 0 (24 + j) (after b14 bodyS).mem = some (.reg .rdx, j)) ∧
    (∀ j < 8, findWrite 0 (32 + j) (after b14 bodyS).mem = some (.reg .rcx, j)) ∧
    (after b14 bodyS).reg .rdi = some (.lit 1) ∧ (after b14 bodyS).reg .rsi = some (.lit 0) ∧
    (after b14 bodyS).reg .rdx = some (.reg .r12) ∧ (after b14 bodyS).reg .rcx = some (.reg .r15) ∧
    (after b14 bodyS).reg .r8 = some (.reg .r13) ∧
    [Reg64.rbp, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b14 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

public theorem ok_b11 : MidOk 112 8 slots (after b11 bodyS) = true ∧ (after b11 bodyS).mem = [] ∧
    [Reg64.rax, .rbp, .r8, .rsi, .rdx, .rcx, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b11 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel
public theorem ok_b12 : MidOk 112 8 slots (after b12 bodyS) = true ∧ (after b12 bodyS).mem = [] ∧
    (after b12 bodyS).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem ok_b13 : EpiOk 112 slots (after b13 bodyS) = true ∧ (after b13 bodyS).mem = [] ∧
    (after b13 bodyS).reg .rax = some (.reg .rax) := by
  decide +kernel
public theorem ok_b15 : MidOk 112 8 slots (after b15 bodyS) = true ∧ (after b15 bodyS).mem = [] ∧
    (after b15 bodyS).reg .rax = some (.lit 0) ∧
    [Reg64.rbp, .r12, .r13, .rbx, .r14, .r15].all
      (fun r ↦ (after b15 bodyS).reg r == some (.reg r)) = true := by
  decide +kernel

/-- `b16`: the `Decoded` at the frame's bytes 40 to 63, `verify`'s arguments. -/
public theorem ok_b16 : MidOk 112 0 slots (after b16 bodyS) = true ∧
    (∀ w ∈ (after b16 bodyS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 40 ≤ w.off ∧ w.off + w.n ≤ 64)) ∧
    (∀ j < 8, findWrite 0 (40 + j) (after b16 bodyS).mem = some (.reg .r12, j)) ∧
    (∀ j < 8, findWrite 0 (48 + j) (after b16 bodyS).mem = some (.reg .r15, j)) ∧
    (∀ j < 8, findWrite 0 (56 + j) (after b16 bodyS).mem = some (.reg .rbx, j)) ∧
    (after b16 bodyS).reg .rdi = some (.ite (.cmp .eq .W64 (.bin .and .W64 (.reg .r14) (.reg .r14))
      (.lit 0)) (.lit 8) (.reg .rbp)) ∧
    (after b16 bodyS).reg .rsi = some (.reg .r14) ∧ (after b16 bodyS).reg .rdx = some (.ptr 0 8) ∧
    (after b16 bodyS).reg .rcx = some (.ptr 0 40) ∧ (after b16 bodyS).reg .r8 = some (.reg .r13) := by
  decide +kernel
public theorem ok_b17 : MidOk 112 8 slots (after b17 bodyS) = true ∧ (after b17 bodyS).mem = [] ∧
    (after b17 bodyS).reg .rax = some (.un (.zext .W8) .W32 (.reg .rax)) := by
  decide +kernel

end NativeRustcVmX64.Top.Leanvm
