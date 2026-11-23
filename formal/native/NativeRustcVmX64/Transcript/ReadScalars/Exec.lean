module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateReadScalars
public import NativeRustcVmX64.Code.Vm.TStateReadScalars.Names
public meta import NativeRustcVmX64.Code.Vm.TStateReadScalars
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::read_scalars`' blocks, run by the symbolic executor (x86-64)

Region 0 the 80-byte frame (R15 to RBX pushed at offsets `72` to `40`, `read_scalar`'s output at
`16`, its return address at `0`) and the return address. `entryS` at the entry: `b0` (the
prologue, BL = `1`, `n = 0`?), then `b1` (the output's end R14 and cursor R15, the `TState` R12,
the output's slot R13). The loop: `callS` at `b2` (`call read_scalar`); `doneS` at `b3` (the
output's tag); `storeS` at `b4` (region 1 the 16 bytes at the cursor: the element stored, the
cursor advanced, against the end). The ends, from `doneS`: `b7` (EAX = EBX, the epilogue), `b5`
then `b7` after the last element, `b6` (EBX = `0`) then `b7` on a rejection.
-/

namespace NativeRustcVmX64.Transcript.ReadScalars

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadScalars

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .r15), (64, .r14), (56, .r13), (48, .r12), (40, .rbx)]

def entryS : SState := init [88] [(.rsp, .ptr 0 80)]
def S0 : SState := after b0 entryS
def callS : SState := init [88] [(.rsp, .ptr 0 8), (.r13, .ptr 0 16)]
def storeS : SState := init [88, 16] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0)]
def doneS : SState := init [88] [(.rsp, .ptr 0 8)]

/-- The output's end, as `b1` computes it. -/
def endSym : Sym := .bin .add .W64 (.reg .rsi) (.bin .shl .W64 (.reg .rdx) (.lit 4))

/-- An end's epilogue: the registers restored, nothing written, RAX's value. -/
def EndOk (S : SState) (v : Sym) : Prop :=
  EpiOk 80 slots S = true ∧ S.mem = [] ∧ S.reg .rax = some v

instance (S : SState) (v : Sym) : Decidable (EndOk S v) := by unfold EndOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 doneS
sym_block run_b4 := exec b4 storeS
sym_block run_b6 := exec b6 (after b3 doneS)
sym_block run_b7r := exec b7 (after b6 (after b3 doneS))
sym_block run_b5 := exec b5 doneS
sym_block run_b7e := exec b7 (after b5 doneS)
sym_block run_b7 := exec b7 doneS

public theorem exit_b0 : exec b0 entryS = some (S0, .cond
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0))
    NativeRustcVmX64.Vm.TStateReadScalars.label_5) :=
  run_b0.trans (by rw [show S0 = _ from after_eq run_b0])
public theorem ok_b0 : ProOk 80 8 slots S0 = true ∧ (∀ w ∈ S0.mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    S0.reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) := by
  decide +kernel
public theorem ok_b1 : ProOk 80 8 slots (after b1 S0) = true ∧
    (∀ w ∈ (after b1 S0).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (after b1 S0).reg .rbx = some (.bin .merge .W8 (.reg .rbx) (.lit 1)) ∧
    (after b1 S0).reg .r14 = some endSym ∧ (after b1 S0).reg .r15 = some (.reg .rsi) ∧
    (after b1 S0).reg .r12 = some (.reg .rdi) ∧ (after b1 S0).reg .r13 = some (.ptr 0 16) := by
  decide +kernel
public theorem ok_b2 : MidOk 80 0 slots (after b2 callS) = true ∧
    (∀ w ∈ (after b2 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 callS).reg .rdi = some (.ptr 0 16) ∧ (after b2 callS).reg .rsi = some (.reg .r12) ∧
    (after b2 callS).reg .r12 = some (.reg .r12) ∧ (after b2 callS).reg .r13 = some (.ptr 0 16) ∧
    (after b2 callS).reg .r14 = some (.reg .r14) ∧ (after b2 callS).reg .r15 = some (.reg .r15) ∧
    (after b2 callS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem exit_b3 : exec b3 doneS = some (after b3 doneS, .cond
    (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.TStateReadScalars.label_4) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 80 8 slots (after b3 doneS) = true ∧ (after b3 doneS).mem = [] ∧
    (after b3 doneS).reg .r12 = some (.reg .r12) ∧ (after b3 doneS).reg .r13 = some (.reg .r13) ∧
    (after b3 doneS).reg .r14 = some (.reg .r14) ∧ (after b3 doneS).reg .r15 = some (.reg .r15) ∧
    (after b3 doneS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem exit_b4 : exec b4 storeS = some (after b4 storeS, .cond
    (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .r14)).not NativeRustcVmX64.Vm.TStateReadScalars.label_2) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem ok_b4 : MidOk 80 8 slots (after b4 storeS) = true ∧
    (∀ t < 8, findWrite 1 t (after b4 storeS).mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b4 storeS).mem = some (.load 0 32 8, t)) ∧
    (∀ w ∈ (after b4 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b4 storeS).reg .r15 = some (.ptr 1 16) ∧ (after b4 storeS).reg .r12 = some (.reg .r12) ∧
    (after b4 storeS).reg .r13 = some (.reg .r13) ∧ (after b4 storeS).reg .r14 = some (.reg .r14) ∧
    (after b4 storeS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem exit_b6 : exec b6 (after b3 doneS) = some (after b6 (after b3 doneS), .fall) :=
  run_b6.trans (by rw [after_eq run_b6])
public theorem exit_b7r : exec b7 (after b6 (after b3 doneS)) =
    some (after b7 (after b6 (after b3 doneS)), .ret (.load 0 80 8)) :=
  run_b7r.trans (by rw [after_eq run_b7r])
public theorem end_r : EndOk (after b7 (after b6 (after b3 doneS))) (.lit 0) := by decide +kernel
public theorem exit_b5 : exec b5 doneS = some (after b5 doneS, .jump NativeRustcVmX64.Vm.TStateReadScalars.label_5) :=
  run_b5.trans (by rw [after_eq run_b5])
public theorem exit_b7e : exec b7 (after b5 doneS) =
    some (after b7 (after b5 doneS), .ret (.load 0 80 8)) :=
  run_b7e.trans (by rw [after_eq run_b7e])
public theorem end_e : EndOk (after b7 (after b5 doneS)) (.un .trunc .W32 (.reg .rbx)) := by
  decide +kernel
public theorem exit_b7 : exec b7 doneS = some (after b7 doneS, .ret (.load 0 80 8)) :=
  run_b7.trans (by rw [after_eq run_b7])
public theorem end_0 : EndOk (after b7 doneS) (.un .trunc .W32 (.reg .rbx)) := by decide +kernel

end NativeRustcVmX64.Transcript.ReadScalars
