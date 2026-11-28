module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateSampleChallenges
public meta import NativeRustcVmArm.Code.Vm.TStateSampleChallenges
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::sample_challenges`'s blocks, run by the symbolic executor

`entryS` at the entry (`b0`: `n = 0` returns at once, `b5`, from `retS`). Otherwise region 0 the
32-byte frame (X30, X21, X20, X19): `proS` at `b1` (the prologue, the output's end in X21, its
cursor in X19); `callS` at `b2`, the loop's head (`bl squeeze`); `storeS` at `b3` (the challenge
stored at the cursor, region 1, the cursor advanced and compared with the end); `epiS` at `b4` (the
epilogue, falling into `b5`).
-/

namespace NativeRustcVmArm.Transcript.SampleChallenges

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateSampleChallenges

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (8, .X21), (16, .X20), (24, .X19)]

def entryS : SState := init [] .sp
def retS : SState := init [] .sp
def proS : SState := init [(32, true)] (.ptr 0 32)
def callS : SState := init [(32, true)] (.ptr 0 0)
def storeS : SState := init [(32, true), (16, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def epiS : SState := init [(32, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 proS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 storeS
sym_block run_b4 := exec b4 epiS
sym_block run_b5 := exec b5 retS

/-- The output's end, `out + 16 n`, as `b1` computes it. -/
@[expose] public def endSym : Sym := .bin .add .W64 (.reg .X1) (.un (.shift .LSL 4) .W64 (.reg .X2))

public theorem ok_b0 : (after b0 entryS).mem = [] ∧ keeps entryS (after b0 entryS) = true := by
  decide +kernel
public theorem ok_b5 : (after b5 retS).mem = [] ∧ keeps retS (after b5 retS) = true ∧
    (after b5 retS).reg .X30 = some (.reg .X30) := by
  decide +kernel
public theorem ok_b1 : ProOk slots (after b1 proS) = true ∧
    (∀ w ∈ (after b1 proS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    (after b1 proS).reg .X19 = some (.reg .X1) ∧ (after b1 proS).reg .X20 = some (.reg .X0) ∧
    (after b1 proS).reg .X21 = some endSym := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 callS) = true ∧ (after b2 callS).mem = [] ∧
    (after b2 callS).reg .X0 = some (.reg .X20) ∧ (after b2 callS).reg .X19 = some (.reg .X19) ∧
    (after b2 callS).reg .X20 = some (.reg .X20) ∧ (after b2 callS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 storeS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b3 storeS).mem = some (.reg .X0, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b3 storeS).mem = some (.reg .X1, t)) ∧
    (∀ w ∈ (after b3 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b3 storeS).reg .X19 = some (.ptr 1 16) ∧ (after b3 storeS).reg .X20 = some (.reg .X20) ∧
    (after b3 storeS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b4 : EpiOk 32 slots (after b4 epiS) = true ∧ (after b4 epiS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Transcript.SampleChallenges
