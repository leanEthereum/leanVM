module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Sumcheck.Common
public import NativeRustcVmX64.Code.Vm.WhirLevels
public import NativeRustcVmX64.Code.Vm.FinalLevel.Names
public import NativeRustcVmX64.Code.Vm.FoldRounds.Names
public import NativeRustcVmX64.Code.Vm.NextLevel.Names
public import NativeRustcVmX64.Code.Vm.WhirLevels.Names
public meta import NativeRustcVmX64.Code.Vm.WhirLevels
public meta import NativeRustcVmX64.Transcript.Frame
public meta import NativeRustcVmX64.Sumcheck.Common

/-!
# `whir_levels`' blocks, run by the symbolic executor (x86-64)

Region 0 is the 112-byte frame below the entry's RSP and the return address (120 bytes; at the
entry also the stack argument `w`, 128 bytes, `argEnv`): RSP at offset `8` in the body, a callee's
return address at `0`, `next_level`'s stack argument at `8`; the words `24` (the last level's
index), `32` (`laneFolds`), `40` (the basis), `48` (`1 - n`), `56` (`logN`); the six pushed
registers from `64`; the return address at `112`, `w` at `120`.

- `entryS` at the entry (`b0`: the prologue, the loop's registers, the frame's words);
- `lvS` at the loop head `NativeRustcVmX64.Vm.WhirLevels.label_1` (`b1`, then `b2`, `fold_rounds`' call), region 1 the
  level at RBX;
- `wS` after `fold_rounds` (`b3`, its test) and at `b4` (`μ`, the last level's test; `b3` changes
  no register), region 1 the state's first 24 bytes at RBP;
- `nxS` at `b5` (`next_level`'s call), region 1 the level and the next one at RBX;
- `retS` after `next_level` (`b6`) and at the exits (`b7`, `b8`).
-/

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.WhirLevels NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

@[expose] public section

/-- The frame's slots: the pushed registers. -/
def slots : Slots := [(104, .rbp), (96, .r15), (88, .r14), (80, .r13), (72, .r12), (64, .rbx)]

/-- At the entry: the frame and the argument word, RSP at offset `112`. -/
def entryS : SState := init [128] [(.rsp, .ptr 0 112)]

/-- In the body: RSP at offset `8`. -/
def retS : SState := init [120] [(.rsp, .ptr 0 8)]

/-- At the loop head: the level (region 1) at RBX. -/
def lvS : SState := init [120, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- After `fold_rounds`: the state's first 24 bytes (region 1) at RBP. -/
def wS : SState := init [120, 24] [(.rsp, .ptr 0 8), (.rbp, .ptr 1 0)]

/-- At `next_level`'s call: the level and the next one (region 1) at RBX. -/
def nxS : SState := init [120, 48] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

/-- `b0`'s `1 - n` (`n ≥ 1`). -/
def v48 : Sym :=
  .bin .sub .W64 (.ite (.cmp .ult .W64 (.reg .r9) (.lit 1)) (.reg .r9) (.lit 1)) (.reg .r9)
/-- `b0`'s `n - 1`, saturated. -/
def v24 : Sym := .ite (.not (.cmp .ult .W64 (.reg .r9) (.lit 1))) (.bin .sub .W64 (.reg .r9) (.lit 1))
  (.lit 0)
/-- `b0`'s `24 n`. -/
def v12 : Sym := .bin .add .W64 (.bin .shl .W64 (.reg .r9) (.lit 3))
  (.bin .mul .W64 (.bin .shl .W64 (.reg .r9) (.lit 3)) (.lit 2))
/-- `b4`'s `μ`: `logN` minus the `α`s, saturated. -/
def v9 : Sym := .ite (.not (.cmp .ult .W64 (.load 0 56 8) (.load 1 16 8)))
  (.bin .sub .W64 (.load 0 56 8) (.load 1 16 8)) (.lit 0)

/-- `b1`'s exit: no level left. -/
def c1 : SBool := .cmp .eq .W64 (.bin .and .W64 (.reg .r12) (.reg .r12)) (.lit 0)
/-- `b3`'s exit: `fold_rounds` rejected. -/
def c3 : SBool := .cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)
/-- `b4`'s exit: the last level. -/
def c4 : SBool :=
  .cmp .eq .W64 (.bin .add .W64 (.reg .r13) (.load 0 48 8)) (.lit 18446744073709551615)
/-- `b6`'s exit: `next_level` accepted. -/
def c6 : SBool := .not (.cmp .eq .W8 (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0))

/-- What the entry leaves: the frame, the words, the loop's registers. -/
def EntryOk (S : SState) : Prop :=
  ProOk 112 8 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 112) ∧
    WordW 0 24 v24 S ∧ WordW 0 32 (.reg .rdx) S ∧ WordW 0 40 (.reg .rcx) S ∧ WordW 0 48 v48 S ∧
    WordW 0 56 (.reg .rsi) S ∧ S.reg .rbx = some (.reg .r8) ∧ S.reg .r12 = some v12 ∧
    S.reg .r13 = some (.lit 18446744073709551615) ∧ S.reg .r15 = some (.reg .rdi) ∧
    S.reg .rbp = some (.load 0 120 8)

instance (S : SState) : Decidable (EntryOk S) := by unfold EntryOk; infer_instance

/-- A body block's writes: region 0 below offset `16`. -/
def Low (S : SState) : Prop := ∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 16

instance (S : SState) : Decidable (Low S) := by unfold Low; infer_instance

/-- The loop's registers kept. -/
def Keeps4 (S : SState) : Prop :=
  S.reg .r12 = some (.reg .r12) ∧ S.reg .r13 = some (.reg .r13) ∧ S.reg .r15 = some (.reg .r15)

instance (S : SState) : Decidable (Keeps4 S) := by unfold Keeps4; infer_instance

/-- `fold_rounds`' call. -/
def FoldOk (S : SState) : Prop :=
  MidOk 112 0 slots S = true ∧ Low S ∧ Keeps4 S ∧ S.reg .rbp = some (.reg .rbp) ∧
    S.reg .rbx = some (.ptr 1 0) ∧ S.reg .rdi = some (.reg .r15) ∧
    S.reg .rsi = some (.load 1 0 8) ∧ S.reg .rdx = some (.reg .rbp) ∧
    S.reg .rcx = some (.bin .add .W64 (.reg .rbp) (.lit 61152))

instance (S : SState) : Decidable (FoldOk S) := by unfold FoldOk; infer_instance

/-- `μ` and the test of the last level. -/
def MuOk (S : SState) : Prop :=
  MidOk 112 8 slots S = true ∧ S.mem = [] ∧ Keeps4 S ∧ S.reg .rbp = some (.ptr 1 0) ∧
    S.reg .rbx = some (.reg .rbx) ∧ S.reg .r9 = some v9

instance (S : SState) : Decidable (MuOk S) := by unfold MuOk; infer_instance

/-- `next_level`'s call. -/
def NextOk (S : SState) : Prop :=
  MidOk 112 0 slots S = true ∧ Low S ∧ WordW 0 8 (.reg .rbp) S ∧ S.reg .rbp = some (.reg .rbp) ∧
    S.reg .r15 = some (.reg .r15) ∧ S.reg .rdi = some (.reg .r15) ∧
    S.reg .rsi = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧ S.reg .rdx = some (.ptr 1 0) ∧
    S.reg .rcx = some (.load 1 24 8) ∧ S.reg .r8 = some (.load 1 32 8) ∧
    S.reg .r9 = some (.reg .r9) ∧
    S.reg .r12 = some (.bin .add .W64 (.lit 18446744073709551592) (.reg .r12)) ∧
    S.reg .r13 = some (.bin .add .W64 (.reg .r13) (.lit 1)) ∧ S.reg .r14 = some (.ptr 1 24)

instance (S : SState) : Decidable (NextOk S) := by unfold NextOk; infer_instance

/-- Back to the loop's head. -/
def BackOk (S : SState) : Prop :=
  MidOk 112 8 slots S = true ∧ S.mem = [] ∧ Keeps4 S ∧ S.reg .rbp = some (.reg .rbp) ∧
    S.reg .rbx = some (.reg .r14)

instance (S : SState) : Decidable (BackOk S) := by unfold BackOk; infer_instance

/-- `None` returned. -/
def NoneOk (S : SState) : Prop :=
  EpiOk 112 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some (.lit 0)

instance (S : SState) : Decidable (NoneOk S) := by unfold NoneOk; infer_instance

/-- The tail call of `final_level`: the registers restored, RSP the entry's, the arguments. -/
def TailOk (S : SState) : Prop :=
  slotsLoaded slots S = true ∧ keepsOthers slots S = true ∧ S.reg .rsp = some (.ptr 0 112) ∧
    S.mem = [] ∧ S.reg .rdi = some (.reg .r15) ∧ S.reg .rsi = some (.load 0 24 8) ∧
    S.reg .rdx = some (.reg .rbx) ∧ S.reg .rcx = some (.reg .r9) ∧
    S.reg .r8 = some (.load 0 32 8) ∧ S.reg .r9 = some (.load 0 40 8)

instance (S : SState) : Decidable (TailOk S) := by unfold TailOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 lvS
sym_block run_b2 := exec b2 (after b1 lvS)
sym_block run_b3 := exec b3 wS
sym_block run_b4 := exec b4 wS
sym_block run_b5 := exec b5 nxS
sym_block run_b6 := exec b6 retS
sym_block run_b7 := exec b7 retS
sym_block run_b8 := exec b8 retS

end NativeRustcVmX64.Whir.Levels.WL

namespace NativeRustcVmX64.Whir.Levels.WL

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.WhirLevels NativeRustcVmX64.Transcript
open NativeRustcVmX64.Sumcheck

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS, .fall) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : EntryOk (after b0 entryS) := by decide +kernel

public theorem exit_b1 : exec b1 lvS = some (after b1 lvS, .cond c1 NativeRustcVmX64.Vm.WhirLevels.label_5) :=
  run_b1.trans (by rw [after_eq run_b1]; rfl)
public theorem exit_b2 : exec b2 (after b1 lvS) = some (after b2 (after b1 lvS),
    .call NativeRustcVmX64.Vm.FoldRounds.entryLabel) :=
  run_b2.trans (by rw [after_eq run_b2])
public theorem ok_b2 : FoldOk (after b2 (after b1 lvS)) := by decide +kernel

public theorem exit_b3 : exec b3 wS = some (after b3 wS, .cond c3 NativeRustcVmX64.Vm.WhirLevels.label_5) :=
  run_b3.trans (by rw [after_eq run_b3]; rfl)
public theorem ok_b3 : MidOk 112 8 slots (after b3 wS) = true ∧ (after b3 wS).mem = [] ∧
    (after b3 wS).regs = wS.regs := by decide +kernel
public theorem exit_b4 : exec b4 wS = some (after b4 wS, .cond c4 NativeRustcVmX64.Vm.WhirLevels.label_6) :=
  run_b4.trans (by rw [after_eq run_b4]; rfl)
public theorem ok_b4 : MuOk (after b4 wS) := by decide +kernel

public theorem exit_b5 : exec b5 nxS =
    some (after b5 nxS, .call NativeRustcVmX64.Vm.NextLevel.entryLabel) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem ok_b5 : NextOk (after b5 nxS) := by decide +kernel

public theorem exit_b6 : exec b6 retS = some (after b6 retS, .cond c6 NativeRustcVmX64.Vm.WhirLevels.label_1) :=
  run_b6.trans (by rw [after_eq run_b6]; rfl)
public theorem ok_b6 : BackOk (after b6 retS) := by decide +kernel

public theorem exit_b7 : exec b7 retS = some (after b7 retS, .ret (.load 0 112 8)) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem ok_b7 : NoneOk (after b7 retS) := by decide +kernel

public theorem exit_b8 : exec b8 retS = some (after b8 retS,
    .jump NativeRustcVmX64.Vm.FinalLevel.entryLabel) :=
  run_b8.trans (by rw [after_eq run_b8])
public theorem ok_b8 : TailOk (after b8 retS) := by decide +kernel

end NativeRustcVmX64.Whir.Levels.WL
