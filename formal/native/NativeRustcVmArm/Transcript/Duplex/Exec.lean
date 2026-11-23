module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.SpongeWDuplex
public meta import NativeRustcVmArm.Code.Vm.SpongeWDuplex
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `SpongeW::duplex`'s blocks, run by the symbolic executor

Region 0 the 16-byte frame (X30, X19), region 1 the sponge: `entryS` at the entry (`b0`, ending in
`bl duplex_input`), `midS` after it (`b1`, ending in `bl keccak_f`; no region but the frame),
`exitS` after `keccak_f` (`b2`: the queue's count zeroed, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.Duplex

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWDuplex

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (8, .X19)]

/-- At the entry: the frame (region 0), the sponge (region 1, X0). -/
def entryS : SState := init [(16, true), (328, false)] (.ptr 0 16) [(.X0, .ptr 1 0)]
/-- After `duplex_input`: the frame. -/
def midS : SState := init [(16, true)] (.ptr 0 0)
/-- After `keccak_f`: the frame, the sponge (region 1, X19). -/
def exitS : SState := init [(16, true), (328, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 midS
sym_block run_b2 := exec b2 exitS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (after b0 entryS).reg .X0 = some (.ptr 1 0) ∧ (after b0 entryS).reg .X19 = some (.ptr 1 0) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 midS) = true ∧ (after b1 midS).mem = [] ∧
    (after b1 midS).reg .X0 = some (.reg .X19) ∧ (after b1 midS).reg .X19 = some (.reg .X19) := by
  decide +kernel
public theorem ok_b2 : EpiOk 16 slots (after b2 exitS) = true ∧
    (∀ t < 8, findWrite 1 (296 + t) (after b2 exitS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b2 exitS).mem, w.r = 1 ∧ 296 ≤ w.off ∧ w.off + w.n ≤ 304) := by
  decide +kernel

end NativeRustcVmArm.Transcript.Duplex
