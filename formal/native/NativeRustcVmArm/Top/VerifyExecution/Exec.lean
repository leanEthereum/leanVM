module

public import NativeRustcVmArm.Top.Frame
public import NativeRustcVmArm.Code.Vm.VerifyExecution
public meta import NativeRustcVmArm.Code.Vm.VerifyExecution

/-!
# `verify_execution`'s blocks, run by the symbolic executor

`verify_execution` (`sub sp, sp, #96`: a 96-byte frame, the prologue's slots at its bytes 16 to
95, the stack argument of `verify_stacked_opening` at its byte 0): the states its proof starts
blocks from and the executor's results (`run_*`):
- `entryS`, at the entry (`b0`: the prologue, ending in `bl read_announced_sizes`): region 0 the
  frame;
- `callS`, at the blocks between the calls (`b1` to `b20`): region 0 the frame (SP), region 1 the
  working area's first 72 bytes (X19), which `b2` (the stack's log-size) and `b14` (`KECCAK`'s
  log-height) read;
- `frameS`, at the epilogue (`b21`): region 0 the frame (SP).
-/

namespace NativeRustcVmArm.Top.VerifyExecution

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.VerifyExecution

@[expose] public section

/-- At the entry: the frame (region 0). -/
def entryS : SState := init [(96, true)] (.ptr 0 96)

/-- Between the calls: the frame (region 0, SP) and the working area's first 72 bytes (region 1,
X19). -/
def callS : SState := init [(96, true), (72, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- The frame (region 0, SP). -/
def frameS : SState := init [(96, true)] (.ptr 0 0)

/-- The prologue's slots in the frame. -/
def slots : List (Nat × XReg) :=
  [(16, .X30), (32, .X26), (40, .X25), (48, .X24), (56, .X23), (64, .X22), (72, .X21), (80, .X20),
    (88, .X19)]

/-- The callee-saved registers outside the slots. -/
def nonslots : List XReg := [.X27, .X28, .X29]

/-- The registers the blocks between the calls keep: the working area's (X19), the `TState`'s
(X20), those outside the slots. -/
def kept : List XReg := [.X19, .X20, .X27, .X28, .X29]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 callS
sym_block run_b4 := exec b4 callS
sym_block run_b5 := exec b5 callS
sym_block run_b6 := exec b6 callS
sym_block run_b7 := exec b7 callS
sym_block run_b8 := exec b8 callS
sym_block run_b9 := exec b9 callS
sym_block run_b10 := exec b10 callS
sym_block run_b11 := exec b11 callS
sym_block run_b12 := exec b12 callS
sym_block run_b13 := exec b13 callS
sym_block run_b14 := exec b14 callS
sym_block run_b15 := exec b15 callS
sym_block run_b16 := exec b16 callS
sym_block run_b17 := exec b17 callS
sym_block run_b18 := exec b18 callS
sym_block run_b19 := exec b19 callS
sym_block run_b20 := exec b20 callS
sym_block run_b21 := exec b21 frameS

public theorem b0_slots : ∀ p ∈ slots, ∀ i < 8,
    findWrite 0 (p.1 + i) (after b0 entryS).mem = some (.reg p.2, i) := by
  decide +kernel

public theorem b0_mem : ∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 96 := by
  decide +kernel

public theorem b0_regs : ∀ r ∈ nonslots, (after b0 entryS).reg r = some (.reg r) := by
  decide +kernel

/-- The blocks between the calls write nothing and keep SP and the registers outside the slots. -/
public theorem call_keeps : ∀ ds ∈ [b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14,
    b15, b16, b17, b19, b20], keepsRegs callS (after ds callS) kept = true ∧
      (after ds callS).mem = [] := by
  decide +kernel

/-- The branches after the calls change no register and write nothing. -/
public theorem branch_keeps : ∀ ds ∈ [b1, b3, b5, b7, b9, b11, b13, b15, b17],
    (after ds callS).regs = callS.regs ∧ (after ds callS).sp = callS.sp ∧
      (after ds callS).mem = [] := by
  decide +kernel

/-- `b18` writes the stack argument, the frame's first word. -/
public theorem b18_keeps : keepsRegs callS (after b18 callS) kept = true ∧
    ∀ w ∈ (after b18 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8 := by
  decide +kernel

public theorem b18_arg : ∀ i < 8,
    findWrite 0 i (after b18 callS).mem = some (.ptr 1 226528, i) := by
  decide +kernel

public theorem b21_restores : restores slots 96 (after b21 frameS) = true ∧
    (after b21 frameS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Top.VerifyExecution
