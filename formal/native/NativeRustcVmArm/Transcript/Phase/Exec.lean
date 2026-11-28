module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.DecodedPhase
public meta import NativeRustcVmArm.Code.Vm.DecodedPhase
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `Decoded::phase`'s blocks, run by the symbolic executor

Region 0 the 32-byte frame (X30, X20, X19), region 1 the `Decoded` struct. `entryS` at the entry
(`b0`: the prologue, `bl phase_count`); `cmpS` at `b1` (`k` against the count and `7`); `noneS` at
`b2` (`None`, the epilogue); `baseS` at `b3` (phase `k`'s base against the length); `someS` at `b5`
(the base's address, the epilogue). `b4` (`None` after `b3`) is never reached.
-/

namespace NativeRustcVmArm.Transcript.Phase

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.DecodedPhase

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (16, .X20), (24, .X19)]

def entryS : SState := init [(32, true)] (.ptr 0 32)
def cmpS : SState := init [(32, true)] (.ptr 0 0)
def noneS : SState := init [(32, true)] (.ptr 0 0)
def baseS : SState := init [(32, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def someS : SState := init [(32, true), (24, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

/-- `streamEnd l + k · phaseWords`, as `b3` computes it in X8. -/
def baseSym : Sym :=
  .bin .add .W64 (.bin .mul .W64 (.reg .X20) (.lit 49411))
    (.bin .orr .W64 (.un (.ubfm 3 63) .W64 (.load 1 16 8)) (.lit 1))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 cmpS
sym_block run_b2 := exec b2 noneS
sym_block run_b3 := exec b3 baseS
sym_block run_b5 := exec b5 someS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) ∧
    (after b0 entryS).reg .X0 = some (.reg .X0) ∧ (after b0 entryS).reg .X19 = some (.reg .X0) ∧
    (after b0 entryS).reg .X20 = some (.reg .X1) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 cmpS) = true ∧ (after b1 cmpS).mem = [] ∧
    (after b1 cmpS).reg .X19 = some (.reg .X19) ∧ (after b1 cmpS).reg .X20 = some (.reg .X20) := by
  decide +kernel
public theorem ok_b2 : EpiOk 32 slots (after b2 noneS) = true ∧ (after b2 noneS).mem = [] ∧
    (after b2 noneS).reg .X0 = some (.lit 0) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 baseS) = true ∧ (after b3 baseS).mem = [] ∧
    (after b3 baseS).reg .X8 = some baseSym ∧ (after b3 baseS).reg .X19 = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b5 : EpiOk 32 slots (after b5 someS) = true ∧ (after b5 someS).mem = [] ∧
    (after b5 someS).reg .X0 = some (.bin .add .W64 (.load 1 0 8)
      (.un (.shift .LSL 3) .W64 (.bin .add .W64 (.reg .X8) (.lit 1)))) := by
  decide +kernel


end NativeRustcVmArm.Transcript.Phase
