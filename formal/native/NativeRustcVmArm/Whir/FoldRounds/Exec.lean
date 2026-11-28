module

public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.FoldRounds
public meta import NativeRustcVmArm.Code.Vm.FoldRounds
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `fold_rounds`'s blocks, run by the symbolic executor

rustc unrolled the loop over the (at most `6`) rounds. `entryS` at the entry (`b0`: the buffer's
count zeroed, region 0 the buffer, `n = 0` returning `1` at once, `b9`, from `retS`). Otherwise
region 0 the 160-byte frame (X30, X23 to X19 at `112` to `160`; `fold_round`'s output at `40`):
`proS` at `b1` (the prologue, `bl fold_round`); `tagS` at each round's tag test (`b2`, `b5`, `b11`,
`b14`, `b17`, `b20`); `storeS` at each round's store (region 1 the buffer: `b3`, `b6`, `b12`, `b15`,
`b18`, `b21`; `StoreOk`), comparing the rounds done with `n`; `callS` at each next round's call
(`b4`, `b10`, `b13`, `b16`, `b19`); `oneS` at `b7` (`1`), `epiS` at `b8` (the epilogue), `failS`
at `b23` (`0`, the epilogue). `b22`, a seventh round, is never reached (`n ≤ 6`).
-/

namespace NativeRustcVmArm.Whir.FoldRounds

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.FoldRounds NativeRustcVmArm.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(112, .X30), (120, .X23), (128, .X22), (136, .X21), (144, .X20), (152, .X19)]

def entryS : SState := init [(8, false)] .sp [(.X3, .ptr 0 0)]
def retS : SState := init [] .sp
def proS : SState := init [(160, true)] (.ptr 0 160)
def tagS : SState := init [(160, true)] (.ptr 0 0)
def storeS : SState :=
  init [(160, true), (200, false)] (.ptr 0 0) [(.X21, .ptr 1 0), (.X23, .ptr 0 40)]
def callS : SState := init [(160, true)] (.ptr 0 0)
def epiS : SState := init [(160, true)] (.ptr 0 0)

/-- What a round's store block does: round `i`'s `α`, `β` (the frame's words `48` to `80`) into
the buffer's item `i - 1`, its count `i`; the registers kept. -/
def StoreOk (i : Nat) (S : SState) : Prop :=
  MidOk slots S = true ∧
    (∀ t < 8, findWrite 1 (0 + t) S.mem = some (.lit i, t)) ∧
    (∀ t < 8, findWrite 1 (8 + 32 * (i - 1) + t) S.mem = some (.load 0 48 8, t)) ∧
    (∀ t < 8, findWrite 1 (16 + 32 * (i - 1) + t) S.mem = some (.load 0 56 8, t)) ∧
    (∀ t < 8, findWrite 1 (24 + 32 * (i - 1) + t) S.mem = some (.load 0 64 8, t)) ∧
    (∀ t < 8, findWrite 1 (32 + 32 * (i - 1) + t) S.mem = some (.load 0 72 8, t)) ∧
    (∀ w ∈ S.mem, (w.r = 1 ∧ w.off + w.n ≤ 8) ∨
      (w.r = 1 ∧ 8 + 32 * (i - 1) ≤ w.off ∧ w.off + w.n ≤ 8 + 32 * i) ∨
      (w.r = 0 ∧ w.off + w.n ≤ 160)) ∧
    S.reg .X19 = some (.reg .X19) ∧ S.reg .X20 = some (.reg .X20) ∧
    S.reg .X21 = some (.ptr 1 0) ∧ S.reg .X22 = some (.reg .X22) ∧ S.reg .X23 = some (.ptr 0 40)

/-- What a round's call block does: `fold_round(sp + 40, t, s)`. -/
def CallOk (S : SState) : Prop :=
  MidOk slots S = true ∧ S.mem = [] ∧ S.reg .X0 = some (.ptr 0 40) ∧
    S.reg .X1 = some (.reg .X20) ∧ S.reg .X2 = some (.reg .X19) ∧
    S.reg .X19 = some (.reg .X19) ∧ S.reg .X20 = some (.reg .X20) ∧
    S.reg .X21 = some (.reg .X21) ∧ S.reg .X22 = some (.reg .X22) ∧ S.reg .X23 = some (.reg .X23)

/-- What a round's tag block does: nothing. -/
def TagOk (S : SState) : Prop :=
  MidOk slots S = true ∧ S.mem = [] ∧
    S.reg .X19 = some (.reg .X19) ∧ S.reg .X20 = some (.reg .X20) ∧
    S.reg .X21 = some (.reg .X21) ∧ S.reg .X22 = some (.reg .X22) ∧ S.reg .X23 = some (.reg .X23)

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 proS
sym_block run_b2 := exec b2 tagS
sym_block run_b3 := exec b3 storeS
sym_block run_b4 := exec b4 callS
sym_block run_b5 := exec b5 tagS
sym_block run_b6 := exec b6 storeS
sym_block run_b7 := exec b7 epiS
sym_block run_b8 := exec b8 epiS
sym_block run_b9 := exec b9 retS
sym_block run_b10 := exec b10 callS
sym_block run_b11 := exec b11 tagS
sym_block run_b12 := exec b12 storeS
sym_block run_b13 := exec b13 callS
sym_block run_b14 := exec b14 tagS
sym_block run_b15 := exec b15 storeS
sym_block run_b16 := exec b16 callS
sym_block run_b17 := exec b17 tagS
sym_block run_b18 := exec b18 storeS
sym_block run_b19 := exec b19 callS
sym_block run_b20 := exec b20 tagS
sym_block run_b21 := exec b21 storeS
sym_block run_b23 := exec b23 epiS

public theorem ok_b0 : keeps entryS (after b0 entryS) = true ∧
    (∀ t < 8, findWrite 0 (0 + t) (after b0 entryS).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 8) := by
  decide +kernel
public theorem ok_b9 : (after b9 retS).mem = [] ∧ keeps retS (after b9 retS) = true ∧
    (after b9 retS).reg .X30 = some (.reg .X30) ∧ (after b9 retS).reg .X0 = some (.lit 1) := by
  decide +kernel
public theorem ok_b1 : ProOk slots (after b1 proS) = true ∧
    (∀ w ∈ (after b1 proS).mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 160) ∧
    (after b1 proS).reg .X0 = some (.ptr 0 40) ∧ (after b1 proS).reg .X1 = some (.reg .X0) ∧
    (after b1 proS).reg .X2 = some (.reg .X2) ∧ (after b1 proS).reg .X19 = some (.reg .X2) ∧
    (after b1 proS).reg .X20 = some (.reg .X0) ∧ (after b1 proS).reg .X21 = some (.reg .X3) ∧
    (after b1 proS).reg .X22 = some (.reg .X1) ∧ (after b1 proS).reg .X23 = some (.ptr 0 40) := by
  decide +kernel
public theorem ok_b2 : TagOk (after b2 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b5 : TagOk (after b5 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b11 : TagOk (after b11 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b14 : TagOk (after b14 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b17 : TagOk (after b17 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b20 : TagOk (after b20 tagS) := by unfold TagOk; decide +kernel
public theorem ok_b3 : StoreOk 1 (after b3 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b3_x0 : (after b3 storeS).reg .X0 = some (.lit 1) := by decide +kernel
public theorem ok_b6 : StoreOk 2 (after b6 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b12 : StoreOk 3 (after b12 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b15 : StoreOk 4 (after b15 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b18 : StoreOk 5 (after b18 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b21 : StoreOk 6 (after b21 storeS) := by unfold StoreOk; decide +kernel
public theorem ok_b4 : CallOk (after b4 callS) := by unfold CallOk; decide +kernel
public theorem ok_b10 : CallOk (after b10 callS) := by unfold CallOk; decide +kernel
public theorem ok_b13 : CallOk (after b13 callS) := by unfold CallOk; decide +kernel
public theorem ok_b16 : CallOk (after b16 callS) := by unfold CallOk; decide +kernel
public theorem ok_b19 : CallOk (after b19 callS) := by unfold CallOk; decide +kernel
public theorem ok_b7 : MidOk slots (after b7 epiS) = true ∧ (after b7 epiS).mem = [] ∧
    (after b7 epiS).reg .X0 = some (.lit 1) := by
  decide +kernel
public theorem ok_b8 : EpiOk 160 slots (after b8 epiS) = true ∧ (after b8 epiS).mem = [] ∧
    (after b8 epiS).reg .X0 = some (.reg .X0) := by
  decide +kernel
public theorem ok_b23 : EpiOk 160 slots (after b23 epiS) = true ∧ (after b23 epiS).mem = [] ∧
    (after b23 epiS).reg .X0 = some (.lit 0) := by
  decide +kernel

end NativeRustcVmArm.Whir.FoldRounds
