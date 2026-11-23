module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.ReadOod
public meta import NativeRustcVmArm.Code.Vm.ReadOod
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `read_ood`'s blocks, run by the symbolic executor

Region 0 the 64-byte frame (`read_scalar`'s output at `8`; X30, X21, X20, X19 at `32` to `56`).
`entryS` at the entry (`b0`: the prologue, X21 `stack_log`, X20 the `TState`, X19 the output,
`bl grind` with `15` bits); `retS` from `grind`'s and `read_scalar`'s returns (region 1 the
output's 504 bytes at X19: `b1` tests `stack_log < 31` and `grind`'s result, `b2` stores the
length and calls `sample_challenges` on the output's buffer; `b4` tests `read_scalar`'s tag, `b5`
stores the value at `488`, returns `1`; `b6` returns `0`); `callS` from `sample_challenges`'s
return (`b3`: `bl read_scalar` into the frame).
-/

namespace NativeRustcVmArm.Layout.ReadOod

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.ReadOod NativeRustcVmArm.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (40, .X21), (48, .X20), (56, .X19)]

def entryS : SState := init [(64, true)] (.ptr 0 64)
def retS : SState := init [(64, true), (504, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def callS : SState := init [(64, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS
sym_block run_b2 := exec b2 (after b1 retS)
sym_block run_b6a := exec b6 (after b1 retS)
sym_block run_b3 := exec b3 callS
sym_block run_b4 := exec b4 retS
sym_block run_b5 := exec b5 (after b4 retS)
sym_block run_b6b := exec b6 (after b4 retS)

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 32 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    (after b0 entryS).reg .X0 = some (.reg .X0) ∧ (after b0 entryS).reg .X1 = some (.lit 15) ∧
    (after b0 entryS).reg .X19 = some (.reg .X2) ∧ (after b0 entryS).reg .X20 = some (.reg .X0) ∧
    (after b0 entryS).reg .X21 = some (.reg .X1) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 retS) = true ∧ (after b1 retS).mem = [] := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 (after b1 retS)) = true ∧
    (after b2 (after b1 retS)).reg .X0 = some (.reg .X20) ∧
    (after b2 (after b1 retS)).reg .X1 = some (.ptr 1 8) ∧
    (after b2 (after b1 retS)).reg .X2 = some (.reg .X21) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b2 (after b1 retS)).mem = some (.reg .X21, t)) ∧
    (∀ w ∈ (after b2 (after b1 retS)).mem, w.r = 1 ∧ w.off = 0 ∧ w.n = 8) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 callS) = true ∧ (after b3 callS).mem = [] ∧
    (after b3 callS).reg .X0 = some (.ptr 0 8) ∧ (after b3 callS).reg .X1 = some (.reg .X20) := by
  decide +kernel
public theorem ok_b4 : MidOk slots (after b4 retS) = true ∧ (after b4 retS).mem = [] := by
  decide +kernel
public theorem ok_b5 : EpiOk 64 slots (after b5 (after b4 retS)) = true ∧
    (after b5 (after b4 retS)).reg .X0 = some (.lit 1) ∧
    (∀ t < 8, findWrite 1 (488 + t) (after b5 (after b4 retS)).mem = some (.load 0 16 8, t)) ∧
    (∀ t < 8, findWrite 1 (496 + t) (after b5 (after b4 retS)).mem = some (.load 0 24 8, t)) ∧
    (∀ w ∈ (after b5 (after b4 retS)).mem, w.r = 1 ∧ 488 ≤ w.off ∧ w.off + w.n ≤ 504) := by
  decide +kernel
public theorem ok_b6a : EpiOk 64 slots (after b6 (after b1 retS)) = true ∧
    (after b6 (after b1 retS)).mem = [] ∧ (after b6 (after b1 retS)).reg .X0 = some (.lit 0) := by
  decide +kernel
public theorem ok_b6b : EpiOk 64 slots (after b6 (after b4 retS)) = true ∧
    (after b6 (after b4 retS)).mem = [] ∧ (after b6 (after b4 retS)).reg .X0 = some (.lit 0) := by
  decide +kernel

end NativeRustcVmArm.Layout.ReadOod
