module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce
public meta import NativeRustcVmArm.Code.Vm.SpongeWAbsorbNonce
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `SpongeW::absorb_nonce`'s blocks, run by the symbolic executor

Region 0 the 16-byte frame (X30, X19), region 1 the sponge. `entryS` at the entry (`b0`: the
prologue, the tag `4` in W3, `bl absorb`); `callS` at `b1` (`bl duplex`); `exitS` at `b2` (the third
lane into X0, the first two stored as the ground challenge with tag `1`, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.AbsorbNonce

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWAbsorbNonce

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (8, .X19)]

def entryS : SState := init [(16, true), (328, false)] (.ptr 0 16) [(.X0, .ptr 1 0)]
def callS : SState := init [(16, true)] (.ptr 0 0)
def exitS : SState := init [(16, true), (328, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 exitS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b0 entryS).reg .X0 = some (.ptr 1 0) ∧ (after b0 entryS).reg .X1 = some (.reg .X1) ∧
    (after b0 entryS).reg .X2 = some (.reg .X2) ∧ (after b0 entryS).reg .X3 = some (.lit 4) ∧
    (after b0 entryS).reg .X19 = some (.ptr 1 0) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 callS) = true ∧ (after b1 callS).mem = [] ∧
    (after b1 callS).reg .X0 = some (.reg .X19) ∧ (after b1 callS).reg .X19 = some (.reg .X19) := by
  decide +kernel
public theorem ok_b2 : EpiOk 16 slots (after b2 exitS) = true ∧
    (after b2 exitS).reg .X0 = some (.load 1 16 8) ∧
    (∀ t < 8, findWrite 1 (304 + t) (after b2 exitS).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 1 (312 + t) (after b2 exitS).mem = some (.load 1 0 8, t)) ∧
    (∀ t < 8, findWrite 1 (320 + t) (after b2 exitS).mem = some (.load 1 8 8, t)) ∧
    (∀ w ∈ (after b2 exitS).mem, w.r = 1 ∧ 304 ≤ w.off ∧ w.off + w.n ≤ 328) := by
  decide +kernel

end NativeRustcVmArm.Transcript.AbsorbNonce
