module

public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb.Names
public import NativeRustcVmArm.Transcript.FrameRun
public import NativeRustcVmArm.Code.Vm.SpongeWAbsorb
public meta import NativeRustcVmArm.Code.Vm.SpongeWAbsorb
public meta import NativeRustcVmArm.Transcript.FrameRun

/-!
# `SpongeW::absorb`'s blocks, run by the symbolic executor

Region 0 the 48-byte frame (X30, X22, X21, X20, X19); region 1 the sponge. `entryS` at the entry
(`b0`: the prologue, the count against `4`); `callS` at `b1` (`bl duplex`); `reloadS` at `b2` (the
count reloaded, against `3`); `pushS n` at `b3` with the count `n` in X8 (the scalar and its tag
stored in slot `n`, the count `n + 1`); `exitS` at `b4` (the epilogue).
-/

namespace NativeRustcVmArm.Transcript.Absorb

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.SpongeWAbsorb

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(0, .X30), (16, .X22), (24, .X21), (32, .X20), (40, .X19)]

def entryS : SState := init [(48, true), (328, false)] (.ptr 0 48) [(.X0, .ptr 1 0)]
def callS : SState := init [(48, true)] (.ptr 0 0)
def reloadS : SState := init [(48, true), (328, false)] (.ptr 0 0) [(.X20, .ptr 1 0)]
def pushS (n : Nat) : SState :=
  init [(48, true), (328, false)] (.ptr 0 0) [(.X20, .ptr 1 0), (.X8, .lit n)]
def exitS : SState := init [(48, true)] (.ptr 0 0)

/-- What `b0` leaves. -/
def B0Ok (S : SState) (x : Exit) : Prop :=
  ProOk slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 48) ∧
    S.reg .X8 = some (.load 1 296 8) ∧ S.reg .X19 = some (.reg .X3) ∧
    S.reg .X20 = some (.ptr 1 0) ∧ S.reg .X21 = some (.reg .X2) ∧ S.reg .X22 = some (.reg .X1) ∧
    x = .cond (.cmp .ult .W64 (.load 1 296 8) (.lit 4)) NativeRustcVmArm.Vm.SpongeWAbsorb.label_2

/-- What `b3` leaves for the count `n`. -/
def PushOk (n : Nat) (S : SState) : Prop :=
  MidOk slots S = true ∧
    (∀ t < 8, findWrite 1 (296 + t) S.mem = some (.lit (n + 1), t)) ∧
    (∀ t < 8, findWrite 1 (200 + 24 * n + t) S.mem = some (.reg .X22, t)) ∧
    (∀ t < 8, findWrite 1 (208 + 24 * n + t) S.mem = some (.reg .X21, t)) ∧
    (∀ t < 8, findWrite 1 (216 + 24 * n + t) S.mem = some (.reg .X19, t)) ∧
    (∀ w ∈ S.mem, w.r = 1 ∧ ((200 + 24 * n ≤ w.off ∧ w.off + w.n ≤ 224 + 24 * n) ∨
      (296 ≤ w.off ∧ w.off + w.n ≤ 304)))

instance (S : SState) (x : Exit) : Decidable (B0Ok S x) := by unfold B0Ok; infer_instance
instance (n : Nat) (S : SState) : Decidable (PushOk n S) := by unfold PushOk; infer_instance

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 callS
sym_block run_b2 := exec b2 reloadS
sym_block run_b3_0 := exec b3 (pushS 0)
sym_block run_b3_1 := exec b3 (pushS 1)
sym_block run_b3_2 := exec b3 (pushS 2)
sym_block run_b3_3 := exec b3 (pushS 3)
sym_block run_b4 := exec b4 exitS

public theorem ok_b0 : ∃ x, exec b0 entryS = some (after b0 entryS, x) ∧ B0Ok (after b0 entryS) x :=
  ⟨_, run_b0.trans (by rw [after_eq run_b0]), by rw [after_eq run_b0]; decide +kernel⟩
public theorem ok_b1 : MidOk slots (after b1 callS) = true ∧ (after b1 callS).mem = [] ∧
    (after b1 callS).reg .X0 = some (.reg .X20) ∧ (after b1 callS).reg .X20 = some (.reg .X20) ∧
    (after b1 callS).reg .X19 = some (.reg .X19) ∧ (after b1 callS).reg .X21 = some (.reg .X21) ∧
    (after b1 callS).reg .X22 = some (.reg .X22) := by
  decide +kernel
public theorem ok_b2 : MidOk slots (after b2 reloadS) = true ∧ (after b2 reloadS).mem = [] ∧
    (after b2 reloadS).reg .X8 = some (.load 1 296 8) ∧
    (after b2 reloadS).reg .X20 = some (.ptr 1 0) ∧ (after b2 reloadS).reg .X19 = some (.reg .X19) ∧
    (after b2 reloadS).reg .X21 = some (.reg .X21) ∧ (after b2 reloadS).reg .X22 = some (.reg .X22) := by
  decide +kernel
public theorem run_b3 : ∀ n < 4, exec b3 (pushS n) = some (after b3 (pushS n), .fall) ∧
    PushOk n (after b3 (pushS n)) := by
  intro n hn
  match n, hn with
  | 0, _ => exact ⟨run_b3_0.trans (by rw [after_eq run_b3_0]), by rw [after_eq run_b3_0]; decide +kernel⟩
  | 1, _ => exact ⟨run_b3_1.trans (by rw [after_eq run_b3_1]), by rw [after_eq run_b3_1]; decide +kernel⟩
  | 2, _ => exact ⟨run_b3_2.trans (by rw [after_eq run_b3_2]), by rw [after_eq run_b3_2]; decide +kernel⟩
  | 3, _ => exact ⟨run_b3_3.trans (by rw [after_eq run_b3_3]), by rw [after_eq run_b3_3]; decide +kernel⟩
public theorem ok_b4 : EpiOk 48 slots (after b4 exitS) = true ∧ (after b4 exitS).mem = [] := by
  decide +kernel

end NativeRustcVmArm.Transcript.Absorb
