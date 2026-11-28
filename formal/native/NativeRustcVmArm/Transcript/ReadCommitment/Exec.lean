module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateReadCommitment
public meta import NativeRustcVmArm.Code.Vm.TStateReadCommitment
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::read_commitment`'s blocks, run by the symbolic executor

Region 0 the 80-byte frame (X30, X23, X22, X21, X20, X19 at `32` to `80`; `read_scalar`'s output at
`8`). `entryS` at the entry (`b0`: the prologue, `bl read_scalar`); `tagS` at `b1` and `b3` (the
tag tested); `callS` at `b2` (the first element into X23, X22, `bl read_scalar`); `countS` at `b4`
(region 1 the `TState`: the roots' count against `8`); `pushS` at `b5` (region 1 the new root's 48
bytes at `X19 + 368 + 48 X8`, region 2 the count at `X19 + 752`, both through aliases: the root
stored, the count advanced, the epilogue); `failS` at `b6` (`0`, the epilogue).
-/

namespace NativeRustcVmArm.Transcript.ReadCommitment

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateReadCommitment

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(32, .X30), (40, .X23), (48, .X22), (56, .X21), (64, .X20), (72, .X19)]

/-- The root's address minus `368`, as `b5` computes it. -/
def rootSym : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X8) (.lit 48)) (.reg .X19)

def entryS : SState := init [(80, true)] (.ptr 0 80)
def tagS : SState := init [(80, true)] (.ptr 0 0)
def callS : SState := init [(80, true)] (.ptr 0 0)
def countS : SState := init [(80, true), (760, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
def pushS : SState := init [(80, true), (48, false), (8, false)] (.ptr 0 0)
  (aliases := [(rootSym, (1, -368)), (.reg .X19, (2, -752))])
def failS : SState := init [(80, true)] (.ptr 0 0)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tagS
sym_block run_b2 := exec b2 callS
sym_block run_b3 := exec b3 tagS
sym_block run_b4 := exec b4 countS
sym_block run_b5 := exec b5 pushS
sym_block run_b6 := exec b6 failS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 80) ∧
    (after b0 entryS).reg .X0 = some (.ptr 0 8) ∧ (after b0 entryS).reg .X1 = some (.reg .X0) ∧
    (after b0 entryS).reg .X19 = some (.reg .X0) ∧ (after b0 entryS).reg .X20 = some (.reg .X2) ∧
    (after b0 entryS).reg .X21 = some (.reg .X1) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 tagS) = true ∧ (after b1 tagS).mem = [] ∧
    (∀ r, calleeSaved r = true → (after b1 tagS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b2 : MidOk slots (after b2 callS) = true ∧ (after b2 callS).mem = [] ∧
    (after b2 callS).reg .X0 = some (.ptr 0 8) ∧ (after b2 callS).reg .X1 = some (.reg .X19) ∧
    (after b2 callS).reg .X23 = some (.load 0 16 8) ∧
    (after b2 callS).reg .X22 = some (.load 0 24 8) ∧
    (∀ r, calleeSaved r = true → r ≠ .X23 → r ≠ .X22 → (after b2 callS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro r hr h23 h22
  cases r <;> first | exact absurd hr (by decide) | exact absurd rfl h23 | exact absurd rfl h22 |
    decide +kernel
public theorem ok_b3 : MidOk slots (after b3 tagS) = true ∧ (after b3 tagS).mem = [] ∧
    (∀ r, calleeSaved r = true → (after b3 tagS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b4 : MidOk slots (after b4 countS) = true ∧ (after b4 countS).mem = [] ∧
    (after b4 countS).reg .X8 = some (.load 1 752 8) ∧ (after b4 countS).reg .X19 = some (.ptr 1 0) ∧
    (∀ r, calleeSaved r = true → (after b4 countS).reg r = some (.reg r) ∨ r = .X19) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | exact Or.inr rfl | exact Or.inl (by decide +kernel)
public theorem ok_b5 : EpiOk 80 slots (after b5 pushS) = true ∧ (after b5 pushS).reg .X0 = some (.lit 1) ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b5 pushS).mem = some (.reg .X23, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b5 pushS).mem = some (.reg .X22, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b5 pushS).mem = some (.load 0 16 8, t)) ∧
    (∀ t < 8, findWrite 1 (24 + t) (after b5 pushS).mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 1 (32 + t) (after b5 pushS).mem = some (.reg .X21, t)) ∧
    (∀ t < 8, findWrite 1 (40 + t) (after b5 pushS).mem = some (.reg .X20, t)) ∧
    (∀ t < 8, findWrite 2 (0 + t) (after b5 pushS).mem =
      some (.bin .add .W64 (.load 2 0 8) (.lit 1), t)) ∧
    (∀ w ∈ (after b5 pushS).mem, (w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 48) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 8)) := by
  decide +kernel
public theorem ok_b6 : EpiOk 80 slots (after b6 failS) = true ∧ (after b6 failS).mem = [] ∧
    (after b6 failS).reg .X0 = some (.lit 0) := by
  decide +kernel

end NativeRustcVmArm.Transcript.ReadCommitment
