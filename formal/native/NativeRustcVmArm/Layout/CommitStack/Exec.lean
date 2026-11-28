module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.CommitStack
public meta import NativeRustcVmArm.Code.Vm.CommitStack
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `commit_stack`'s blocks, run by the symbolic executor

Region 0 the 192-byte frame (`ladder`'s result at `0` to `160`; X30, X20, X19 at `160`, `176`,
`184`). `entryS` at the entry (`b0`: the prologue, X19 the `TState`, X20 `μ`, `bl ladder` on the
frame); `retS` from the return (`b1`: the tag; `b2`: the count in `1..6`; `b3`: the epilogue, `0`;
`b4`: level `0`'s shape into X1, X2, the epilogue, the tail call of `read_commitment`).
-/

namespace NativeRustcVmArm.Layout.CommitStack

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.CommitStack NativeRustcVmArm.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(160, .X30), (176, .X20), (184, .X19)]

def entryS : SState := init [(192, true)] (.ptr 0 192)
def retS : SState := init [(192, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS
sym_block run_b2 := exec b2 (after b1 retS)
sym_block run_b3 := exec b3 (after b1 retS)
sym_block run_b4 := exec b4 (after b2 (after b1 retS))

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 160 ≤ w.off ∧ w.off + w.n ≤ 192) ∧
    (after b0 entryS).reg .X0 = some (.ptr 0 0) ∧ (after b0 entryS).reg .X1 = some (.reg .X1) ∧
    (after b0 entryS).reg .X2 = some (.reg .X2) ∧ (after b0 entryS).reg .X19 = some (.reg .X0) ∧
    (after b0 entryS).reg .X20 = some (.reg .X1) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 retS) = true ∧ (after b1 retS).mem = [] ∧
    (∀ r, calleeSaved r = true → (after b1 retS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b2 : MidOk slots (after b2 (after b1 retS)) = true ∧
    (after b2 (after b1 retS)).mem = [] ∧
    (∀ r, calleeSaved r = true → (after b2 (after b1 retS)).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b3 : EpiOk 192 slots (after b3 (after b1 retS)) = true ∧
    (after b3 (after b1 retS)).mem = [] ∧ (after b3 (after b1 retS)).reg .X0 = some (.lit 0) := by
  decide +kernel
public theorem ok_b4 : EpiOk 192 slots (after b4 (after b2 (after b1 retS))) = true ∧
    (after b4 (after b2 (after b1 retS))).mem = [] ∧
    (after b4 (after b2 (after b1 retS))).reg .X0 = some (.reg .X19) ∧
    (after b4 (after b2 (after b1 retS))).reg .X1 = some (.bin .add .W64
      (.ite (.cmp .ult .W64 (.reg .X20) (.load 0 8 8)) (.lit 0)
        (.bin .sub .W64 (.reg .X20) (.load 0 8 8))) (.load 0 16 8)) ∧
    (after b4 (after b2 (after b1 retS))).reg .X2 = some (.bin .lslv .W64 (.lit 1) (.load 0 8 8)) := by
  decide +kernel

end NativeRustcVmArm.Layout.CommitStack
