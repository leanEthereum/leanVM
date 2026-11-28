module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.SpongeWSqueeze
public meta import NativeRustcVmArm.Code.Vm.SpongeWSqueeze
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `SpongeW::squeeze`'s blocks, run by the symbolic executor

Region 0 the 16-byte frame (X30, X19), region 1 the sponge. `entryS` at the entry (`b0`: the
ground challenge loaded into X0, X1, its tag zeroed, branching on the tag's bit `0`); `callS` at
`b1` (`bl duplex`); `loadS` at `b2` (the first two lanes into X0, X1); `exitS` at `b3` (the
epilogue).
-/

namespace NativeRustcVmArm.Transcript.Squeeze

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWSqueeze

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (8, .X19)]

def entryS : SState := init [(16, true), (328, false)] (.ptr 0 16) [(.X0, .ptr 1 0)]
def callS : SState := init [(16, true)] (.ptr 0 0)
def loadS : SState := init [(16, true), (328, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def exitS : SState := init [(16, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 loadS
sym_block run_b3 := exec b3 exitS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .X0 = some (.load 1 312 8) ∧
    (after b0 entryS).reg .X1 = some (.load 1 320 8) ∧
    (after b0 entryS).reg .X19 = some (.ptr 1 0) ∧
    (∀ t < 8, findWrite 1 (304 + t) (after b0 entryS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b0 entryS).mem, (w.r = 1 ∧ 304 ≤ w.off ∧ w.off + w.n ≤ 312) ∨
      (w.r = 0 ∧ w.off + w.n ≤ 16)) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 callS) = true ∧ (after b1 callS).mem = [] ∧
    (after b1 callS).reg .X0 = some (.reg .X19) ∧ (after b1 callS).reg .X19 = some (.reg .X19) := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 loadS) = true ∧ (after b2 loadS).mem = [] ∧
    (after b2 loadS).reg .X0 = some (.load 1 0 8) ∧ (after b2 loadS).reg .X1 = some (.load 1 8 8) := by
  decide +kernel
public theorem ok_b3 : EpiOk 16 slots (after b3 exitS) = true ∧ (after b3 exitS).mem = [] ∧
    (after b3 exitS).reg .X0 = some (.reg .X0) ∧ (after b3 exitS).reg .X1 = some (.reg .X1) := by
  decide +kernel

end NativeRustcVmArm.Transcript.Squeeze
