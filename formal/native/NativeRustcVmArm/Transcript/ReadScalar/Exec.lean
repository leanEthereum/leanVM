module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateReadScalar
public meta import NativeRustcVmArm.Code.Vm.TStateReadScalar
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::read_scalar`'s blocks, run by the symbolic executor

Region 0 the 80-byte frame (X30 at `32`, X22, X21, X20, X19 at `48` to `80`; `next_scalar`'s output
at `8`). `entryS` at the entry (`b0`: the prologue, `bl next_scalar`); `tagS` at `b1` (its tag
tested); `callS` at `b2` (the element into X21, X22, `bl absorb` with the tag `1`); `storeS` at `b3`
(the element and the tag `1` stored at the output, region 1, the epilogue); `noneS` at `b4` (the
tag `0` stored, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.ReadScalar

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadScalar

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (48, .X22), (56, .X21), (64, .X20), (72, .X19)]

def entryS : SState := init [(80, true)] (.ptr 0 80)
def tagS : SState := init [(80, true)] (.ptr 0 0)
def callS : SState := init [(80, true)] (.ptr 0 0)
def storeS : SState := init [(80, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def noneS : SState := init [(80, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tagS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 storeS
sym_block run_b4 := exec b4 noneS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 80) ∧
    (after b0 entryS).reg .X0 = some (.ptr 0 8) ∧ (after b0 entryS).reg .X1 = some (.reg .X1) ∧
    (after b0 entryS).reg .X19 = some (.reg .X0) ∧ (after b0 entryS).reg .X20 = some (.reg .X1) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 tagS) = true ∧ (after b1 tagS).mem = [] ∧
    (after b1 tagS).reg .X19 = some (.reg .X19) ∧ (after b1 tagS).reg .X20 = some (.reg .X20) := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 callS) = true ∧ (after b2 callS).mem = [] ∧
    (after b2 callS).reg .X0 = some (.reg .X20) ∧ (after b2 callS).reg .X1 = some (.load 0 16 8) ∧
    (after b2 callS).reg .X2 = some (.load 0 24 8) ∧ (after b2 callS).reg .X3 = some (.lit 1) ∧
    (after b2 callS).reg .X19 = some (.reg .X19) ∧ (after b2 callS).reg .X20 = some (.lit 1) ∧
    (after b2 callS).reg .X21 = some (.load 0 16 8) ∧
    (after b2 callS).reg .X22 = some (.load 0 24 8) := by
  decide +kernel
public theorem ok_b3 : EpiOk 80 slots (after b3 storeS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b3 storeS).mem = some (.reg .X20, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b3 storeS).mem = some (.reg .X21, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b3 storeS).mem = some (.reg .X22, t)) ∧
    (∀ w ∈ (after b3 storeS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel
public theorem ok_b4 : EpiOk 80 slots (after b4 noneS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b4 noneS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b4 noneS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel


end NativeRustcVmArm.Transcript.ReadScalar
