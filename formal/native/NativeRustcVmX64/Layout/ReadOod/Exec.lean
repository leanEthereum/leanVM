module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.ReadOod
public import NativeRustcVmX64.Code.Vm.ReadOod.Names
public import NativeRustcVmX64.Code.Vm.TStateGrind.Names
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public meta import NativeRustcVmX64.Code.Vm.ReadOod
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `read_ood`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 64-byte frame and the return address (R15, R14, RBX pushed at `56`, `48`, `40`;
`read_scalar`'s output at `16`; the calls' return addresses at `0`). `entryS` at the entry (`b0`:
the prologue, RBX the output, R15 `stack_log`, R14 the `TState`, `call grind` with `15` bits);
`outS` from `grind`'s and `read_scalar`'s returns (region 1 the output's 504 bytes at RBX: `b1`
tests `stack_log ≤ 30`, `b2` `grind`'s result, `b3` stores the length and calls
`sample_challenges` on the output's buffer; `b5` tests `read_scalar`'s tag, `b6` stores the value
at `488`, AL = `1`; `b7` AL = `0`; `b8` the epilogue); `callS` from `sample_challenges`'s return
(`b4`: `call read_scalar` into the frame).
-/

namespace NativeRustcVmX64.Layout.ReadOod

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.ReadOod NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(56, .r15), (48, .r14), (40, .rbx)]

def entryS : SState := init [72] [(.rsp, .ptr 0 64)]
def outS : SState := init [72, 504] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def callS : SState := init [72] [(.rsp, .ptr 0 8)]
def S1 : SState := after b1 outS
def S2 : SState := after b2 S1
def S5 : SState := after b5 outS
def S6 : SState := after b6 S5
def S7 : SState := after b7 S5

/-- `grind`'s result's low byte is `0`, as `b2` tests it. -/
def failSym : SBool :=
  .cmp .eq .W8 (.bin .and .W8 (.un .trunc .W32 (.reg .rax)) (.un .trunc .W32 (.reg .rax))) (.lit 0)

/-- `stack_log > 30`, as `b1` tests it. -/
def bigSym : SBool :=
  (SBool.cmp .ult .W64 (.reg .r15) (.lit 30)).not.and (SBool.cmp .eq .W64 (.reg .r15) (.lit 30)).not

/-- An end: the registers restored, nothing written, RAX's value. -/
def EndOk (S : SState) (v : Sym) : Prop :=
  EpiOk 64 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some v

instance (S : SState) (v : Sym) : Decidable (EndOk S v) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 outS
sym_block run_b8a := exec b8 S1
sym_block run_b2 := exec b2 S1
sym_block run_b8b := exec b8 S2
sym_block run_b3 := exec b3 S2
sym_block run_b4 := exec b4 callS
sym_block run_b5 := exec b5 outS
sym_block run_b7 := exec b7 S5
sym_block run_b8c := exec b8 S7
sym_block run_b6 := exec b6 S5
sym_block run_b8d := exec b8 S6

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.TStateGrind.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 64 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) ∧ (after b0 entryS).reg .rsi = some (.lit 15) ∧
    (after b0 entryS).reg .rbx = some (.reg .rdx) ∧ (after b0 entryS).reg .r14 = some (.reg .rdi) ∧
    (after b0 entryS).reg .r15 = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b1 : exec b1 outS = some (S1, .cond bigSym NativeRustcVmX64.Vm.ReadOod.label_5) :=
  run_b1.trans (by rw [show S1 = _ from after_eq run_b1]; rfl)
public theorem exit_b8a : exec b8 S1 = some (after b8 S1, .ret (.load 0 64 8)) :=
  run_b8a.trans (by rw [after_eq run_b8a])
public theorem end_b8a : EndOk (after b8 S1) (.lit 0) := by decide +kernel
public theorem exit_b2 : exec b2 S1 = some (S2, .cond failSym NativeRustcVmX64.Vm.ReadOod.label_5) :=
  run_b2.trans (by rw [show S2 = _ from after_eq run_b2]; rfl)
public theorem exit_b8b : exec b8 S2 = some (after b8 S2, .ret (.load 0 64 8)) :=
  run_b8b.trans (by rw [after_eq run_b8b])
public theorem end_b8b : EndOk (after b8 S2) (.lit 0) := by decide +kernel
public theorem exit_b3 : exec b3 S2 = some (after b3 S2,
    .call NativeRustcVmX64.Vm.TStateSampleChallenges.entryLabel) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 64 0 slots (after b3 S2) = true ∧
    (∀ w ∈ (after b3 S2).mem, (w.r = 0 ∧ w.off + w.n ≤ 8) ∨ (w.r = 1 ∧ w.off + w.n ≤ 8)) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b3 S2).mem = some (.reg .r15, t)) ∧
    (after b3 S2).reg .rdi = some (.reg .r14) ∧ (after b3 S2).reg .rsi = some (.ptr 1 8) ∧
    (after b3 S2).reg .rdx = some (.reg .r15) ∧ (after b3 S2).reg .rbx = some (.ptr 1 0) ∧
    (after b3 S2).reg .r14 = some (.reg .r14) := by
  decide +kernel
public theorem exit_b4 : exec b4 callS = some (after b4 callS,
    .call NativeRustcVmX64.Vm.TStateReadScalar.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 64 0 slots (after b4 callS) = true ∧
    (∀ w ∈ (after b4 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b4 callS).reg .rdi = some (.ptr 0 16) ∧ (after b4 callS).reg .rsi = some (.reg .r14) ∧
    (after b4 callS).reg .rbx = some (.reg .rbx) ∧ (after b4 callS).reg .r14 = some (.reg .r14) := by
  decide +kernel
public theorem exit_b5 : exec b5 outS = some (S5,
    .cond (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.ReadOod.label_4) :=
  run_b5.trans (by rw [show S5 = _ from after_eq run_b5])
public theorem exit_b7 : exec b7 S5 = some (S7, .fall) :=
  run_b7.trans (by rw [show S7 = _ from after_eq run_b7])
public theorem exit_b8c : exec b8 S7 = some (after b8 S7, .ret (.load 0 64 8)) :=
  run_b8c.trans (by rw [after_eq run_b8c])
public theorem end_b8c : EndOk (after b8 S7) (.lit 0) := by decide +kernel
public theorem exit_b6 : exec b6 S5 = some (S6, .jump NativeRustcVmX64.Vm.ReadOod.label_5) :=
  run_b6.trans (by rw [show S6 = _ from after_eq run_b6])
public theorem exit_b8d : exec b8 S6 = some (after b8 S6, .ret (.load 0 64 8)) :=
  run_b8d.trans (by rw [after_eq run_b8d])
public theorem end_b8d : EpiOk 64 slots (after b8 S6) = true ∧
    (after b8 S6).reg .rax = some (.bin .merge .W8 (.load 0 24 8) (.lit 1)) ∧
    (∀ t < 8, findWrite 1 (488 + t) (after b8 S6).mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 1 (496 + t) (after b8 S6).mem = some (.load 0 32 8, t)) ∧
    (∀ w ∈ (after b8 S6).mem, w.r = 1 ∧ 488 ≤ w.off ∧ w.off + w.n ≤ 504) := by
  decide +kernel

end NativeRustcVmX64.Layout.ReadOod
