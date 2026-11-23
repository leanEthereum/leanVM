module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.GkrLayers
public import NativeRustcVmX64.Code.Vm.GkrLayers.Names
public import NativeRustcVmX64.Code.Vm.GkrStep.Names
public meta import NativeRustcVmX64.Code.Vm.GkrLayers
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `gkr_layers`'s blocks, run by the symbolic executor (x86-64)

Region 0 is the 48-byte frame below the entry's RSP and the return address (`Frame`, `F = 48`):
R15 to RBX pushed at offsets `40` to `16`, RAX at `8` (alignment), RSP at offset `8` in the body,
`gkr_step`'s return address at `0`. `entryS` at the entry (`b0`: the prologue, BL = `1`,
`depth = 0`?); `headS` everywhere else: `b1` (the `TState` R15, `depth` R12, the `GkrStateW` R14),
the loop's head `b6` (one level left?), `b7` (`depth` even?), the steps `b3`, `b8` (calls) and their
checks `b4`, `b5`, `b9`, `b10`, `b11`; `b12` the tail call `gkr_step(t, 1, true, s)`; `b13` (BL = `0`)
and `b14` (EAX = EBX, the epilogue).
-/

namespace NativeRustcVmX64.Bus.GkrLayers

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.GkrLayers NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

/-- At the entry. -/
def entryS : SState := init [56] [(.rsp, .ptr 0 48)]
/-- In the body. -/
def headS : SState := init [56] [(.rsp, .ptr 0 8)]

/-- `test %al, %al`: zero. -/
def cAl : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)

/-- The callee-saved registers a body block keeps. -/
def Keeps (S : SState) (rs : List Reg64) : Bool := rs.all fun r ↦ S.reg r == some (.reg r)

/-- A body block: the frame kept (RSP at `o`), no write but a call's return address. -/
def BodyOk (o : Nat) (S : SState) : Bool :=
  MidOk 48 o slots S && S.mem.all (fun w ↦ w.r == 0 && decide (w.off + w.n ≤ 8))

/-- `last`: `depth - 2 = 0`, as `b3` sets DL. -/
def lastS : Sym :=
  .bin .merge .W8 (.lit 0) (.ite (.cmp .eq .W64 (.bin .add .W64 (.lit 18446744073709551614)
    (.reg .r12)) (.lit 0)) (.lit 1) (.lit 0))

/-- `depth - 2`. -/
def subTwo : Sym := .bin .add .W64 (.lit 18446744073709551614) (.reg .r12)

/-- `depth - 1`. -/
def subOne : Sym := .bin .sub .W64 (.reg .r12) (.lit 1)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 headS
sym_block run_b3 := exec b3 headS
sym_block run_b4 := exec b4 headS
sym_block run_b5 := exec b5 headS
sym_block run_b6 := exec b6 headS
sym_block run_b7 := exec b7 headS
sym_block run_b8 := exec b8 headS
sym_block run_b9 := exec b9 headS
sym_block run_b10 := exec b10 headS
sym_block run_b11 := exec b11 headS
sym_block run_b12 := exec b12 headS
sym_block run_b13 := exec b13 headS
sym_block run_b14 := exec b14 headS

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .rsi) (.reg .rsi)) (.lit 0)) NativeRustcVmX64.Vm.GkrLayers.label_11) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 48 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b0 entryS).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) ∧
    Keeps (after b0 entryS) [.rsi, .rdx, .rdi] = true := by
  decide +kernel

public theorem exit_b1 : exec b1 headS = some (after b1 headS, .jump NativeRustcVmX64.Vm.GkrLayers.label_4) :=
  run_b1.trans (by rw [after_eq run_b1])
public theorem ok_b1 : BodyOk 8 (after b1 headS) = true ∧ (after b1 headS).mem = [] ∧
    (after b1 headS).reg .r12 = some (.reg .rsi) ∧ (after b1 headS).reg .r14 = some (.reg .rdx) ∧
    (after b1 headS).reg .r15 = some (.reg .rdi) ∧ Keeps (after b1 headS) [.rbx] = true := by
  decide +kernel

public theorem exit_b3 : exec b3 headS = some (after b3 headS,
    .call NativeRustcVmX64.Vm.GkrStep.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : BodyOk 0 (after b3 headS) = true ∧
    (after b3 headS).reg .rdi = some (.reg .r15) ∧ (after b3 headS).reg .rsi = some (.lit 2) ∧
    (after b3 headS).reg .rdx = some lastS ∧ (after b3 headS).reg .rcx = some (.reg .r14) ∧
    (after b3 headS).reg .r12 = some subTwo ∧ Keeps (after b3 headS) [.rbx, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b4 : exec b4 headS = some (after b4 headS, .cond cAl NativeRustcVmX64.Vm.GkrLayers.label_10) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : BodyOk 8 (after b4 headS) = true ∧ (after b4 headS).mem = [] ∧
    Keeps (after b4 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b5 : exec b5 headS = some (after b5 headS,
    .cond (.cmp .eq .W64 (.bin .and .W64 (.reg .r12) (.reg .r12)) (.lit 0)) NativeRustcVmX64.Vm.GkrLayers.label_11) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : BodyOk 8 (after b5 headS) = true ∧ (after b5 headS).mem = [] ∧
    Keeps (after b5 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b6 : exec b6 headS = some (after b6 headS,
    .cond (.cmp .eq .W64 (.reg .r12) (.lit 1)) NativeRustcVmX64.Vm.GkrLayers.label_8) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem ok_b6 : BodyOk 8 (after b6 headS) = true ∧ (after b6 headS).mem = [] ∧
    Keeps (after b6 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b7 : exec b7 headS = some (after b7 headS,
    .cond (.cmp .eq .W8 (.bin .and .W8 (.reg .r12) (.lit 1)) (.lit 0)) NativeRustcVmX64.Vm.GkrLayers.label_2) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : BodyOk 8 (after b7 headS) = true ∧ (after b7 headS).mem = [] ∧
    Keeps (after b7 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b8 : exec b8 headS = some (after b8 headS,
    .call NativeRustcVmX64.Vm.GkrStep.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : BodyOk 0 (after b8 headS) = true ∧
    (after b8 headS).reg .rdi = some (.reg .r15) ∧ (after b8 headS).reg .rsi = some (.lit 1) ∧
    (after b8 headS).reg .rdx = some (.lit 0) ∧ (after b8 headS).reg .rcx = some (.reg .r14) ∧
    Keeps (after b8 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b9 : exec b9 headS = some (after b9 headS, .cond cAl NativeRustcVmX64.Vm.GkrLayers.label_10) :=
  run_b9.trans (by rw [after_eq run_b9]; rfl)
public theorem ok_b9 : BodyOk 8 (after b9 headS) = true ∧ (after b9 headS).mem = [] ∧
    Keeps (after b9 headS) [.rbx, .r12, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b10 : exec b10 headS = some (after b10 headS,
    .cond (SBool.cmp .eq .W64 (.bin .and .W64 subOne subOne) (.lit 0)).not NativeRustcVmX64.Vm.GkrLayers.label_4) :=
  run_b10.trans (by rw [after_eq run_b10]; rfl)
public theorem ok_b10 : BodyOk 8 (after b10 headS) = true ∧ (after b10 headS).mem = [] ∧
    (after b10 headS).reg .r12 = some subOne ∧
    Keeps (after b10 headS) [.rbx, .r14, .r15] = true := by
  decide +kernel

public theorem exit_b11 : exec b11 headS = some (after b11 headS, .jump NativeRustcVmX64.Vm.GkrLayers.label_11) :=
  run_b11.trans (by rw [after_eq run_b11])
public theorem ok_b11 : BodyOk 8 (after b11 headS) = true ∧ (after b11 headS).mem = [] ∧
    Keeps (after b11 headS) [.rbx] = true := by
  decide +kernel

public theorem exit_b12 : exec b12 headS = some (after b12 headS,
    .jump NativeRustcVmX64.Vm.GkrStep.entryLabel) :=
  run_b12.trans (by rw [after_eq run_b12])
public theorem ok_b12 : slotsLoaded slots (after b12 headS) = true ∧
    keepsOthers slots (after b12 headS) = true ∧
    (after b12 headS).reg .rsp = some (.ptr 0 48) ∧ (after b12 headS).mem = [] ∧
    (after b12 headS).reg .rdi = some (.reg .r15) ∧ (after b12 headS).reg .rsi = some (.lit 1) ∧
    (after b12 headS).reg .rdx = some (.lit 1) ∧ (after b12 headS).reg .rcx = some (.reg .r14) := by
  decide +kernel

public theorem exit_b13 : exec b13 headS = some (after b13 headS, .fall) :=
  run_b13.trans (by rw [after_eq run_b13])
public theorem ok_b13 : BodyOk 8 (after b13 headS) = true ∧ (after b13 headS).mem = [] ∧
    (after b13 headS).reg .rbx = some (.lit 0) := by
  decide +kernel

public theorem exit_b14 : exec b14 headS = some (after b14 headS, .ret (.load 0 48 8)) :=
  run_b14.trans (by rw [after_eq run_b14])
public theorem ok_b14 : EpiOk 48 slots (after b14 headS) = true ∧ (after b14 headS).mem = [] ∧
    (after b14 headS).reg .rax = some (.un .trunc .W32 (.reg .rbx)) := by
  decide +kernel

end NativeRustcVmX64.Bus.GkrLayers
