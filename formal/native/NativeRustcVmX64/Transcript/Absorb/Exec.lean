module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb
public import NativeRustcVmX64.Code.Vm.SpongeWAbsorb.Names
public meta import NativeRustcVmX64.Code.Vm.SpongeWAbsorb
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `SpongeW::absorb`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 48-byte frame (R15, R14, R12, RBX pushed at offsets `40` to `16`, RAX at `8`, the
call's return address at `0`) and the return address; region 1 the sponge. `entryS` at the entry
(`b0`: the prologue, the count against `4`); `callS` at `b1` (`call duplex`); `reloadS` at `b2`
(the count reloaded, against `3`); `pushS n` at `b3` with the count `n` in RAX (the scalar and its
tag stored in slot `n`, the count `n + 1`); `exitS` at `b4` (the epilogue).
-/

namespace NativeRustcVmX64.Transcript.Absorb

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.SpongeWAbsorb

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(40, .r15), (32, .r14), (24, .r12), (16, .rbx)]

def entryS : SState := init [56, 328] [(.rsp, .ptr 0 48), (.rdi, .ptr 1 0)]
def callS : SState := init [56] [(.rsp, .ptr 0 8)]
def reloadS : SState := init [56, 328] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def pushS (n : Nat) : SState :=
  init [56, 328] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.rax, .lit n)]
def exitS : SState := init [56] [(.rsp, .ptr 0 8)]

/-- What `b0` leaves. -/
def B0Ok (S : SState) (x : Exit) : Prop :=
  ProOk 48 8 slots S = true ∧ (∀ w ∈ S.mem, w.r = 0 ∧ w.off + w.n ≤ 48) ∧
    S.reg .rax = some (.load 1 296 8) ∧ S.reg .rbx = some (.ptr 1 0) ∧
    S.reg .r12 = some (.reg .rsi) ∧
    S.reg .r15 = some (.reg .rdx) ∧ S.reg .r14 = some (.reg .rcx) ∧
    x = .cond (.cmp .ult .W64 (.load 1 296 8) (.lit 4)) NativeRustcVmX64.Vm.SpongeWAbsorb.label_2

/-- What `b3` leaves for the count `n`. -/
def PushOk (n : Nat) (S : SState) : Prop :=
  MidOk 48 8 slots S = true ∧
    (∀ t < 8, findWrite 1 (296 + t) S.mem = some (.lit (n + 1), t)) ∧
    (∀ t < 8, findWrite 1 (200 + 24 * n + t) S.mem = some (.reg .r12, t)) ∧
    (∀ t < 8, findWrite 1 (208 + 24 * n + t) S.mem = some (.reg .r15, t)) ∧
    (∀ t < 8, findWrite 1 (216 + 24 * n + t) S.mem = some (.reg .r14, t)) ∧
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
public theorem ok_b1 : MidOk 48 0 slots (after b1 callS) = true ∧
    (∀ w ∈ (after b1 callS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b1 callS).reg .rdi = some (.reg .rbx) ∧ (after b1 callS).reg .rbx = some (.reg .rbx) ∧
    (after b1 callS).reg .r12 = some (.reg .r12) ∧ (after b1 callS).reg .r14 = some (.reg .r14) ∧
    (after b1 callS).reg .r15 = some (.reg .r15) := by
  decide +kernel
public theorem ok_b2 : MidOk 48 8 slots (after b2 reloadS) = true ∧ (after b2 reloadS).mem = [] ∧
    (after b2 reloadS).reg .rax = some (.load 1 296 8) ∧
    (after b2 reloadS).reg .rbx = some (.ptr 1 0) ∧ (after b2 reloadS).reg .r12 = some (.reg .r12) ∧
    (after b2 reloadS).reg .r14 = some (.reg .r14) ∧
    (after b2 reloadS).reg .r15 = some (.reg .r15) := by
  decide +kernel
public theorem exit_b2 : exec b2 reloadS = some (after b2 reloadS,
    .cond ((SBool.cmp .ult .W64 (.load 1 296 8) (.lit 3)).not.and
      (SBool.cmp .eq .W64 (.load 1 296 8) (.lit 3)).not) NativeRustcVmX64.Vm.SpongeWAbsorb.label_3) :=
  run_b2.trans (by rw [after_eq run_b2])
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

end NativeRustcVmX64.Transcript.Absorb
