module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateGrind
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public meta import NativeRustcVmX64.Code.Vm.TStateGrind
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::grind`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 48-byte frame (R14, RBX pushed at offsets `40`, `32`, `next_scalar`'s output at `8`,
the calls' return addresses at `0`) and the return address. `entryS` at the entry: `b0`
(`bits = 0`?), then `b5` (AL = `1`, `ret`) or `b1` (the prologue, EBX = `bits`, R14 the `TState`,
`call next_scalar`). From `doneS` after it: `b2` (the output's tag), then `b6` (`0`, the epilogue)
or `b3` (`call absorb_nonce` on the element). From `doneS` after it: `b4` (AL = the proof of
work's test, the epilogue).
-/

namespace NativeRustcVmX64.Transcript.Grind

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateGrind

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r14), (32, .rbx)]

def entryS : SState := init [56] [(.rsp, .ptr 0 48)]
def S0 : SState := after b0 entryS
def doneS : SState := init [56] [(.rsp, .ptr 0 8)]
def D2 : SState := after b2 doneS

/-- The proof of work's test, `pow & !(-1 << bits) == 0`, in AL after `b4`. -/
def okSym : Sym :=
  .bin .merge .W8 (.reg .rax) (.ite (.cmp .eq .W64 (.bin .and .W64 (.reg .rax)
    (.un .not .W64 (.bin .shl .W64 (.lit 18446744073709551615) (.un .trunc .W32 (.reg .rbx)))))
    (.lit 0)) (.lit 1) (.lit 0))

/-- An end: the registers restored, nothing written, RAX's value. -/
def EndOk (S : SState) (v : Sym) : Prop :=
  EpiOk 48 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some v

instance (S : SState) (v : Sym) : Decidable (EndOk S v) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b5 := exec b5 S0
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 doneS
sym_block run_b6 := exec b6 D2
sym_block run_b3 := exec b3 D2
sym_block run_b4 := exec b4 doneS

public theorem exit_b0 : exec b0 entryS = some (S0, .cond
    (SBool.cmp .eq .W32 (.bin .and .W32 (.reg .rsi) (.reg .rsi)) (.lit 0)) NativeRustcVmX64.Vm.TStateGrind.label_3) :=
  run_b0.trans (by rw [show S0 = _ from after_eq run_b0])
public theorem exit_b5 : exec b5 S0 = some (after b5 S0, .ret (.load 0 48 8)) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : keeps entryS (after b5 S0) = true ∧ (after b5 S0).mem = [] ∧
    (after b5 S0).reg .rsp = some (.ptr 0 56) ∧
    (after b5 S0).reg .rax = some (.bin .merge .W8 (.reg .rax) (.lit 1)) := by
  decide +kernel
public theorem ok_b1 : ProOk 48 0 slots (after b1 S0) = true ∧
    (∀ w ∈ (after b1 S0).mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    (after b1 S0).reg .rdi = some (.ptr 0 8) ∧ (after b1 S0).reg .rsi = some (.reg .rdi) ∧
    (after b1 S0).reg .rbx = some (.un .trunc .W32 (.reg .rsi)) ∧
    (after b1 S0).reg .r14 = some (.reg .rdi) := by
  decide +kernel
public theorem exit_b2 : exec b2 doneS = some (D2, .cond
    (SBool.cmp .eq .W8 (.load 0 8 1) (.lit 0)) NativeRustcVmX64.Vm.TStateGrind.label_4) :=
  run_b2.trans (by rw [show D2 = _ from after_eq run_b2])
public theorem ok_b2 : MidOk 48 8 slots D2 = true ∧ D2.mem = [] ∧
    D2.reg .rbx = some (.reg .rbx) ∧ D2.reg .r14 = some (.reg .r14) := by
  decide +kernel
public theorem exit_b6 : exec b6 D2 = some (after b6 D2, .ret (.load 0 48 8)) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem end_b6 : EndOk (after b6 D2) (.lit 0) := by decide +kernel
public theorem ok_b3 : MidOk 48 0 slots (after b3 D2) = true ∧
    (∀ w ∈ (after b3 D2).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b3 D2).reg .rdi = some (.reg .r14) ∧ (after b3 D2).reg .rsi = some (.load 0 16 8) ∧
    (after b3 D2).reg .rdx = some (.load 0 24 8) ∧ (after b3 D2).reg .rbx = some (.reg .rbx) ∧
    (after b3 D2).reg .r14 = some (.reg .r14) := by
  decide +kernel
public theorem exit_b4 : exec b4 doneS = some (after b4 doneS, .ret (.load 0 48 8)) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem end_b4 : EndOk (after b4 doneS) okSym := by decide +kernel

end NativeRustcVmX64.Transcript.Grind
