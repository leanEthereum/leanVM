module

public import NativeRustcVmX64.Bus.Facts
public import NativeRustcVmX64.Code.Vm.BlockForm
public import NativeRustcVmX64.Code.Vm.BlockForm.Names
public import NativeRustcVmX64.Code.Vm.Names
public meta import NativeRustcVmX64.Code.Vm.BlockForm
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `block_form`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 80-byte frame (RBP, R15, R14, R13, R12, RBX pushed at offsets `72` to `32`, the
span's end at `16`, the weights' count at `24`, a callee's return address at `0`) and the return
address. `entryS` at the entry (`b0`: the prologue, the form at R9, region 1, the constant
`side_beta`); `tupS` at `b1` (the span from `TUPLES`, region 1, at the tuple RDI); `midS` at the
other blocks; `wS` at `b5` (the slot's weight, region 1, at R15 minus `8`). The loop head is `b8`
(`NativeRustcVmX64.Vm.BlockForm.label_4`).
-/

namespace NativeRustcVmX64.Bus.BlockForm

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.BlockForm
open NativeRustcVmX64.Transcript NativeRustcVmX64.Bus

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .rbp), (64, .r15), (56, .r14), (48, .r13), (40, .r12), (32, .rbx)]


def entryS : SState := init [88, 5928] [(.rsp, .ptr 0 80), (.r9, .ptr 1 0)]
def tupS : SState := init [88, 2352] [(.rsp, .ptr 0 8)] [(NativeRustcVmX64.Vm.Symbols.rodata3Label, 1)] [(.reg .rdi, 147)]
def midS : SState := init [88] [(.rsp, .ptr 0 8)]
def wS : SState := init [88, 16] [(.rsp, .ptr 0 8), (.r15, .ptr 1 8)]

/-- A span word of `TUPLES`, at the tuple RDI. -/
def spanWord (o : Nat) : Sym := slotLoad [] 1 o 16 8 (.reg .rdi) 0 146

/-- `b0`'s exit condition: past `TUPLES`. -/
def c0 : SBool :=
  (SBool.cmp .ult .W64 (.reg .rdi) (.lit 146)).not.and (SBool.cmp .eq .W64 (.reg .rdi) (.lit 146)).not

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tupS
sym_block run_b3 := exec b3 midS
sym_block run_b5 := exec b5 wS
sym_block run_b6 := exec b6 midS
sym_block run_b7 := exec b7 midS
sym_block run_b8 := exec b8 midS
sym_block run_b9 := exec b9 midS
sym_block run_b10 := exec b10 midS
sym_block run_b11 := exec b11 midS
sym_block run_b12 := exec b12 midS

public theorem exit_b0 : (exec b0 entryS).map (·.2) = some (.cond c0 NativeRustcVmX64.Vm.BlockForm.label_1) := by
  rw [run_b0]; rfl

public theorem ok_b0 : ProOk 80 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∨ (w.r = 1 ∧ w.off + w.n ≤ 5928)) ∧
    Wrote 1 [(0, .lit 1), (8, .lit 0), (16, .lit 0), (24, .lit 0), (32, .reg .rcx),
      (40, .reg .r8)] (after b0 entryS) ∧
    Wrote 0 [(24, .reg .rdx)] (after b0 entryS) ∧
    (after b0 entryS).reg .rbx = some (.ptr 1 0) ∧ (after b0 entryS).reg .r15 = some (.reg .rsi) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) := by
  decide +kernel

public theorem ok_b1 : MidOk 80 8 slots (after b1 tupS) = true ∧ (after b1 tupS).mem = [] ∧
    (after b1 tupS).reg .rbp = some (spanWord 0) ∧
    (after b1 tupS).reg .r14 = some (.bin .add .W64 (spanWord 0) (spanWord 8)) ∧
    Keeps [.rbx, .r15] (after b1 tupS) := by
  decide +kernel

public theorem exit_b1 : (exec b1 tupS).map (·.2) = some (.jump NativeRustcVmX64.Vm.BlockForm.label_3) := by
  rw [run_b1]; rfl

public theorem ok_b3 : MidOk 80 8 slots (after b3 midS) = true ∧
    (∀ w ∈ (after b3 midS).mem, w.r = 0 ∧ 16 ≤ w.off ∧ w.off + w.n ≤ 24) ∧
    Wrote 0 [(16, .reg .r14)] (after b3 midS) ∧
    (after b3 midS).reg .r14 = some (.ite (.cmp .ult .W64 (.reg .r14) (.reg .rbp)) (.lit 0)
      (.bin .sub .W64 (.reg .r14) (.reg .rbp))) ∧
    (after b3 midS).reg .r13 = some (.lit 0) ∧
    (after b3 midS).reg .r15 = some (.bin .add .W64 (.lit 8) (.reg .r15)) ∧
    Keeps [.rbx, .rbp] (after b3 midS) := by
  decide +kernel

public theorem exit_b3 : (exec b3 midS).map (·.2) = some (.jump NativeRustcVmX64.Vm.BlockForm.label_4) := by
  rw [run_b3]; rfl

public theorem ok_b8 : MidOk 80 8 slots (after b8 midS) = true ∧ (after b8 midS).mem = [] ∧
    (after b8 midS).reg .r12 = some (.bin .add .W64 (.reg .r13) (.reg .rbp)) ∧
    Keeps [.rbx, .rbp, .r13, .r14, .r15] (after b8 midS) := by
  decide +kernel

public theorem exit_b8 : (exec b8 midS).map (·.2) =
    some (.cond (.cmp .eq .W64 (.reg .r14) (.reg .r13)) NativeRustcVmX64.Vm.BlockForm.label_9) := by
  rw [run_b8]; rfl

public theorem ok_b9 : MidOk 80 0 slots (after b9 midS) = true ∧
    (∀ w ∈ (after b9 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b9 midS).reg .rdi = some (.reg .r12) ∧
    Keeps [.rbx, .rbp, .r12, .r13, .r14, .r15] (after b9 midS) := by
  decide +kernel

public theorem ok_b10 : MidOk 80 8 slots (after b10 midS) = true ∧ (after b10 midS).mem = [] ∧
    Keeps [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b10 midS) := by
  decide +kernel

public theorem exit_b10 : (exec b10 midS).map (·.2) =
    some (.cond (.cmp .ult .W64 (.reg .r13) (.load 0 24 8)) NativeRustcVmX64.Vm.BlockForm.label_7) := by
  rw [run_b10]; rfl

public theorem ok_b11 : MidOk 80 8 slots (after b11 midS) = true ∧ (after b11 midS).mem = [] ∧
    (after b11 midS).reg .rcx = some (.lit 0) ∧ (after b11 midS).reg .r8 = some (.lit 0) ∧
    Keeps [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b11 midS) := by
  decide +kernel

public theorem exit_b11 : (exec b11 midS).map (·.2) = some (.jump NativeRustcVmX64.Vm.BlockForm.label_8) := by
  rw [run_b11]; rfl

public theorem ok_b5 : MidOk 80 8 slots (after b5 wS) = true ∧ (after b5 wS).mem = [] ∧
    (after b5 wS).reg .rcx = some (.load 1 0 8) ∧ (after b5 wS).reg .r8 = some (.load 1 8 8) ∧
    Keeps [.rax, .rdx, .rbx, .rbp, .r12, .r13, .r14] (after b5 wS) ∧
    (after b5 wS).reg .r15 = some (.ptr 1 8) := by
  decide +kernel

public theorem exit_b5 : (exec b5 wS).map (·.2) = some .fall := by
  rw [run_b5]; rfl

public theorem ok_b6 : MidOk 80 0 slots (after b6 midS) = true ∧
    (∀ w ∈ (after b6 midS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b6 midS).reg .rdi = some (.reg .rbx) ∧ (after b6 midS).reg .rsi = some (.reg .rax) ∧
    Keeps [.rdx, .rcx, .r8, .rbx, .rbp, .r12, .r13, .r14, .r15] (after b6 midS) := by
  decide +kernel

public theorem ok_b7 : MidOk 80 8 slots (after b7 midS) = true ∧ (after b7 midS).mem = [] ∧
    (after b7 midS).reg .r15 = some (.bin .add .W64 (.lit 16) (.reg .r15)) ∧
    (after b7 midS).reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧
    Keeps [.rbx, .rbp, .r12, .r14] (after b7 midS) := by
  decide +kernel

public theorem exit_b7 : (exec b7 midS).map (·.2) = some (.cond (.cmp .eq .W8
    (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.BlockForm.label_9) := by
  rw [run_b7]; rfl

public theorem ok_b12 : EpiOk 80 slots (after b12 midS) = true ∧ (after b12 midS).mem = [] ∧
    (after b12 midS).reg .rax = some (.bin .merge .W8 (.reg .rax)
      (.ite (SBool.cmp .ult .W64 (.reg .r12) (.load 0 16 8)).not (.lit 1) (.lit 0))) := by
  decide +kernel

public theorem exit_b12 : (exec b12 midS).map (·.2) = some (.ret (.load 0 80 8)) := by
  rw [run_b12]; rfl

end NativeRustcVmX64.Bus.BlockForm
