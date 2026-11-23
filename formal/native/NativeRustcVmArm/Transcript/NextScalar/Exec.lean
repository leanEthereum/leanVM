module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateNextScalar
public meta import NativeRustcVmArm.Code.Vm.TStateNextScalar
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::next_scalar`'s blocks, run by the symbolic executor

Region 0 the 64-byte frame (X30, X21, X20, X19 at `32` to `64`; `stream_element`'s output at `8`).
`entryS` at the entry (`b0`: the prologue, the ground tag tested; region 1 the `TState`); `zeroS` at
`b1` (`None`'s tag); `storeS` at `b2` (the tag X8 stored at the output, region 1, the epilogue);
`callS` at `b3` (the area, its length and the cursor loaded, `bl stream_element`); `tagS` at `b4`
(`stream_element`'s tag tested); `someS` at `b5` (the cursor advanced in the `TState`, region 1, the
element copied to the output, region 2, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.NextScalar

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateNextScalar

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (40, .X21), (48, .X20), (56, .X19)]

def entryS : SState := init [(64, true), (760, false)] (.ptr 0 64) [(.X1, .ptr 1 0)]
def zeroS : SState := init [(64, true)] (.ptr 0 0)
def storeS : SState := init [(64, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def callS : SState := init [(64, true), (760, false)] (.ptr 0 0) [(.X1, .ptr 1 0)]
def tagS : SState := init [(64, true)] (.ptr 0 0)
def someS : SState :=
  init [(64, true), (760, false), (24, false)] (.ptr 0 0) [(.X21, .ptr 1 0), (.X19, .ptr 2 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 zeroS
sym_block run_b2 := exec b2 storeS
sym_block run_b3 := exec b3 callS
sym_block run_b4 := exec b4 tagS
sym_block run_b5 := exec b5 someS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 64) ∧
    (after b0 entryS).reg .X19 = some (.reg .X0) ∧ (after b0 entryS).reg .X1 = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 zeroS) = true ∧ (after b1 zeroS).mem = [] ∧
    (after b1 zeroS).reg .X8 = some (.lit 0) ∧ (after b1 zeroS).reg .X19 = some (.reg .X19) := by
  decide +kernel
public theorem ok_b2 : EpiOk 64 slots (after b2 storeS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b2 storeS).mem = some (.reg .X8, t)) ∧
    (∀ w ∈ (after b2 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 callS) = true ∧ (after b3 callS).mem = [] ∧
    (after b3 callS).reg .X0 = some (.ptr 0 8) ∧ (after b3 callS).reg .X1 = some (.load 1 328 8) ∧
    (after b3 callS).reg .X2 = some (.load 1 336 8) ∧ (after b3 callS).reg .X3 = some (.load 1 352 8) ∧
    (after b3 callS).reg .X19 = some (.reg .X19) ∧ (after b3 callS).reg .X20 = some (.load 1 352 8) ∧
    (after b3 callS).reg .X21 = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b4 : MidOk slots (after b4 tagS) = true ∧ (after b4 tagS).mem = [] ∧
    (after b4 tagS).reg .X8 = some (.load 0 8 8) ∧ (after b4 tagS).reg .X19 = some (.reg .X19) ∧
    (after b4 tagS).reg .X20 = some (.reg .X20) ∧ (after b4 tagS).reg .X21 = some (.reg .X21) := by
  decide +kernel
public theorem ok_b5 : EpiOk 64 slots (after b5 someS) = true ∧
    (∀ t < 8, findWrite 1 (352 + t) (after b5 someS).mem =
      some (.bin .add .W64 (.reg .X20) (.lit 1), t)) ∧
    (∀ t < 8, findWrite 2 (0 + t) (after b5 someS).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 2 (8 + t) (after b5 someS).mem = some (.load 0 16 8, t)) ∧
    (∀ t < 8, findWrite 2 (16 + t) (after b5 someS).mem = some (.load 0 24 8, t)) ∧
    (∀ w ∈ (after b5 someS).mem, (w.r = 1 ∧ 352 ≤ w.off ∧ w.off + w.n ≤ 360) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 24)) := by
  decide +kernel

end NativeRustcVmArm.Transcript.NextScalar
