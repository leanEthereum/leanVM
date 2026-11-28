module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.TStateQueryOpenings
public meta import NativeRustcVmArm.Code.Vm.TStateQueryOpenings
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `TState::query_openings`'s blocks, run by the symbolic executor

Region 0 the 96-byte frame (X30 at `32`, X24 to X19 at `48` to `88`; `open_phase`'s output at
`0`). `entryS` at the entry (`b0`: the prologue, region 1 the `TState`: the roots' count against
`8`); `cmpS` at `b1` (`i` against the count), `b3` (the phase's address against `0`) and `b5` (the
output's first word against `0`); `phaseS` at `b2` (region 1 the `TState`: the phase index,
`bl phase`); `openS` at `b4` (region 1 root `i`'s 48 bytes at `X24 · 48 + X20 + 368`, through an
alias: `bl open_phase`); `okS` at `b6` (region 1 the output, region 2 the phase index at
`X20 + 360`, through an alias: the rows copied, the index advanced, the epilogue); `failS` at `b7`
(region 1 the output: `0`, the epilogue).
-/

namespace NativeRustcVmArm.Sumcheck.QueryOpenings

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.TStateQueryOpenings
open NativeRustcVmArm.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots :=
  [(32, .X30), (48, .X24), (56, .X23), (64, .X22), (72, .X21), (80, .X20), (88, .X19)]

/-- Root `i`'s address minus `368`, as `b4` computes it. -/
def rootSym : Sym := .bin .add .W64 (.bin .mul .W64 (.reg .X24) (.lit 48)) (.reg .X20)

def entryS : SState := init [(96, true), (760, false)] (.ptr 0 96) [(.X1, .ptr 1 0)]
def cmpS : SState := init [(96, true)] (.ptr 0 0)
def phaseS : SState := init [(96, true), (760, false)] (.ptr 0 0) [(.X1, .ptr 1 0)]
def openS : SState := init [(96, true), (48, false)] (.ptr 0 0)
  (aliases := [(rootSym, (1, -368))])
def okS : SState := init [(96, true), (32, false), (8, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]
  (aliases := [(.reg .X20, (2, -360))])
def failS : SState := init [(96, true), (8, false)] (.ptr 0 0) [(.X19, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 cmpS
sym_block run_b2 := exec b2 phaseS
sym_block run_b3 := exec b3 cmpS
sym_block run_b4 := exec b4 openS
sym_block run_b5 := exec b5 cmpS
sym_block run_b6 := exec b6 okS
sym_block run_b7 := exec b7 failS

public theorem ok_b0 : ProOk slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 96) ∧
    (after b0 entryS).reg .X8 = some (.load 1 752 8) ∧ (after b0 entryS).reg .X19 = some (.reg .X0) ∧
    (after b0 entryS).reg .X1 = some (.ptr 1 0) ∧ (after b0 entryS).reg .X2 = some (.reg .X2) ∧
    (after b0 entryS).reg .X3 = some (.reg .X3) ∧ (after b0 entryS).reg .X4 = some (.reg .X4) := by
  decide +kernel
public theorem ok_b1 : MidOk slots (after b1 cmpS) = true ∧ (after b1 cmpS).mem = [] ∧
    (after b1 cmpS).reg .X24 = some (.reg .X2) ∧ (after b1 cmpS).reg .X1 = some (.reg .X1) ∧
    (after b1 cmpS).reg .X3 = some (.reg .X3) ∧ (after b1 cmpS).reg .X4 = some (.reg .X4) ∧
    (∀ r, calleeSaved r = true → r ≠ .X24 → (after b1 cmpS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  intro r hr h24
  cases r <;> first | exact absurd hr (by decide) | exact absurd rfl h24 | decide +kernel
public theorem ok_b2 : MidOk slots (after b2 phaseS) = true ∧ (after b2 phaseS).mem = [] ∧
    (after b2 phaseS).reg .X0 = some (.ptr 1 328) ∧ (after b2 phaseS).reg .X1 = some (.load 1 360 8) ∧
    (after b2 phaseS).reg .X20 = some (.ptr 1 0) ∧ (after b2 phaseS).reg .X21 = some (.load 1 360 8) ∧
    (after b2 phaseS).reg .X22 = some (.reg .X4) ∧ (after b2 phaseS).reg .X23 = some (.reg .X3) ∧
    (after b2 phaseS).reg .X19 = some (.reg .X19) ∧ (after b2 phaseS).reg .X24 = some (.reg .X24) := by
  decide +kernel
public theorem ok_b3 : MidOk slots (after b3 cmpS) = true ∧ (after b3 cmpS).mem = [] ∧
    (after b3 cmpS).reg .X0 = some (.reg .X0) ∧
    (∀ r, calleeSaved r = true → (after b3 cmpS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b4 : MidOk slots (after b4 openS) = true ∧ (after b4 openS).mem = [] ∧
    (after b4 openS).reg .X0 = some (.ptr 0 0) ∧
    (after b4 openS).reg .X1 = some (.bin .add .W64 rootSym (.lit 368)) ∧
    (after b4 openS).reg .X2 = some (.load 1 32 8) ∧ (after b4 openS).reg .X3 = some (.load 1 40 8) ∧
    (after b4 openS).reg .X4 = some (.reg .X23) ∧ (after b4 openS).reg .X5 = some (.reg .X22) ∧
    (after b4 openS).reg .X6 = some (.reg .X0) ∧
    (∀ r, calleeSaved r = true → (after b4 openS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b5 : MidOk slots (after b5 cmpS) = true ∧ (after b5 cmpS).mem = [] ∧
    (∀ r, calleeSaved r = true → (after b5 cmpS).reg r = some (.reg r)) := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro r hr
  cases r <;> first | exact absurd hr (by decide) | decide +kernel
public theorem ok_b6 : EpiOk 96 slots (after b6 okS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b6 okS).mem = some (.load 0 0 8, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b6 okS).mem = some (.load 0 8 8, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b6 okS).mem = some (.load 0 16 8, t)) ∧
    (∀ t < 8, findWrite 1 (24 + t) (after b6 okS).mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 2 (0 + t) (after b6 okS).mem =
      some (.bin .add .W64 (.reg .X21) (.lit 1), t)) ∧
    (∀ w ∈ (after b6 okS).mem, (w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 32) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 8)) := by
  decide +kernel
public theorem ok_b7 : EpiOk 96 slots (after b7 failS) = true ∧
    (∀ t < 8, findWrite 1 (0 + t) (after b7 failS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b7 failS).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 8) := by
  decide +kernel

end NativeRustcVmArm.Sumcheck.QueryOpenings
