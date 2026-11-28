module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges
public import NativeRustcVmX64.Code.Vm.TStateSampleChallenges.Names
public meta import NativeRustcVmX64.Code.Vm.TStateSampleChallenges
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::sample_challenges`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 32-byte frame (R15, R14, RBX pushed at offsets `24` to `8`, `squeeze`'s return
address at `0`) and the return address. `entryS` at the entry: `b0` (`n = 0`?), then `b5` (`ret`)
or `b1` (the prologue, the output's cursor R14 and end RBX). The loop: `callS` at `b2`
(`call squeeze` on the `TState`, R15); `storeS` at `b3` (region 1 the 16 bytes at the cursor: the
challenge stored, the cursor advanced, against the end); `b4`, `b5` (the epilogue) after the
last.
-/

namespace NativeRustcVmX64.Transcript.SampleChallenges

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateSampleChallenges

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(24, .r15), (16, .r14), (8, .rbx)]

def entryS : SState := init [40] [(.rsp, .ptr 0 32)]
def S0 : SState := after b0 entryS
def callS : SState := init [40] [(.rsp, .ptr 0 8)]
def storeS : SState := init [40, 16] [(.rsp, .ptr 0 8), (.r14, .ptr 1 0)]

/-- The output's end, as `b1` computes it. -/
def endSym : Sym := .bin .add .W64 (.reg .rsi) (.bin .shl .W64 (.reg .rdx) (.lit 4))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b5a := exec b5 S0
sym_block run_b1 := exec b1 S0
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 storeS
sym_block run_b4 := exec b4 callS
sym_block run_b5 := exec b5 (after b4 callS)

public theorem exit_b0 : exec b0 entryS = some (S0, .cond
    (SBool.cmp .eq .W64 (.bin .and .W64 (.reg .rdx) (.reg .rdx)) (.lit 0))
    NativeRustcVmX64.Vm.TStateSampleChallenges.label_4) :=
  run_b0.trans (by rw [show S0 = _ from after_eq run_b0])
public theorem ok_b5a : keeps entryS (after b5 S0) = true ∧ (after b5 S0).mem = [] ∧
    (after b5 S0).reg .rsp = some (.ptr 0 40) := by
  decide +kernel
public theorem exit_b5a : exec b5 S0 = some (after b5 S0, .ret (.load 0 32 8)) :=
  run_b5a.trans (by rw [after_eq run_b5a])
public theorem ok_b1 : ProOk 32 8 slots (after b1 S0) = true ∧
    (∀ w ∈ (after b1 S0).mem, w.r = 0 ∧ w.off + w.n ≤ 32) ∧
    (after b1 S0).reg .rbx = some endSym ∧ (after b1 S0).reg .r14 = some (.reg .rsi) ∧
    (after b1 S0).reg .r15 = some (.reg .rdi) := by
  decide +kernel
public theorem ok_b2 : MidOk 32 0 slots (after b2 callS) = true ∧
    (∀ w ∈ (after b2 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 callS).reg .rdi = some (.reg .r15) ∧ (after b2 callS).reg .r15 = some (.reg .r15) ∧
    (after b2 callS).reg .r14 = some (.reg .r14) ∧ (after b2 callS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem exit_b3 : exec b3 storeS = some (after b3 storeS, .cond
    (SBool.cmp .eq .W64 (.ptr 1 16) (.reg .rbx)).not NativeRustcVmX64.Vm.TStateSampleChallenges.label_2) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem ok_b3 : MidOk 32 8 slots (after b3 storeS) = true ∧
    (∀ t < 8, findWrite 1 t (after b3 storeS).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b3 storeS).mem = some (.reg .rdx, t)) ∧
    (∀ w ∈ (after b3 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b3 storeS).reg .r14 = some (.ptr 1 16) ∧ (after b3 storeS).reg .r15 = some (.reg .r15) ∧
    (after b3 storeS).reg .rbx = some (.reg .rbx) := by
  decide +kernel
public theorem ok_end : EpiOk 32 slots (after b5 (after b4 callS)) = true ∧
    (after b5 (after b4 callS)).mem = [] := by
  decide +kernel
public theorem exit_end : exec b5 (after b4 callS) =
    some (after b5 (after b4 callS), .ret (.load 0 32 8)) :=
  run_b5.trans (by rw [after_eq run_b5])

end NativeRustcVmX64.Transcript.SampleChallenges
