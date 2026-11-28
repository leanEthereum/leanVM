module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateNextScalar
public import NativeRustcVmX64.Code.Vm.TStateNextScalar.Names
public meta import NativeRustcVmX64.Code.Vm.TStateNextScalar
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::next_scalar`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 64-byte frame (R15, R14, RBX pushed at offsets `56` to `40`, `stream_element`'s
output at `16`, its return address at `0`) and the return address, region 1 the `TState`, region 2
the output. From `entryS`: `b0` (the prologue, the ground tag), then either `b4`, `b5` (a ground
challenge waits: the tag `0` stored, the epilogue) or `b1` (`call stream_element` on the area, its
length and the cursor, its output in the frame). From `midS` after it: `b2` (its tag), then `b4`,
`b5` (`None`) or `b3`, `b5` (the cursor advanced, the element copied, the tag `1`).
-/

namespace NativeRustcVmX64.Transcript.NextScalar

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateNextScalar

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(56, .r15), (48, .r14), (40, .rbx)]

def entryS : SState := init [72, 760, 24] [(.rsp, .ptr 0 64), (.rsi, .ptr 1 0), (.rdi, .ptr 2 0)]
def S0 : SState := after b0 entryS
def midS : SState := init [72, 760, 24] [(.rsp, .ptr 0 8), (.r15, .ptr 1 0), (.rbx, .ptr 2 0)]
def M2 : SState := after b2 midS

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 S0
sym_block run_b4a := exec b4 S0
sym_block run_b5a := exec b5 (after b4 S0)
sym_block run_b2 := exec b2 midS
sym_block run_b4b := exec b4 M2
sym_block run_b5b := exec b5 (after b4 M2)
sym_block run_b3 := exec b3 M2
sym_block run_b5c := exec b5 (after b3 M2)

public theorem exit_b0 : exec b0 entryS = some (S0,
    .cond (SBool.cmp .eq .W8 (.load 1 304 1) (.lit 0)).not NativeRustcVmX64.Vm.TStateNextScalar.label_3) :=
  run_b0.trans (by rw [show S0 = _ from after_eq run_b0])
public theorem exit_b2 : exec b2 midS = some (M2,
    .cond (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.TStateNextScalar.label_3) :=
  run_b2.trans (by rw [show M2 = _ from after_eq run_b2])
public theorem ok_b1 : ProOk 64 0 slots (after b1 S0) = true ∧
    (∀ w ∈ (after b1 S0).mem, w.r = 0 ∧ w.off + w.n ≤ 64) ∧
    (after b1 S0).reg .rdi = some (.ptr 0 16) ∧ (after b1 S0).reg .rsi = some (.load 1 328 8) ∧
    (after b1 S0).reg .rdx = some (.load 1 336 8) ∧ (after b1 S0).reg .rcx = some (.load 1 352 8) ∧
    (after b1 S0).reg .r14 = some (.load 1 352 8) ∧ (after b1 S0).reg .r15 = some (.ptr 1 0) ∧
    (after b1 S0).reg .rbx = some (.ptr 2 0) := by
  decide +kernel
/-- A ground challenge waits: the tag `0` stored, the epilogue. -/
public theorem ok_a : keeps entryS (after b5 (after b4 S0)) = true ∧
    (after b5 (after b4 S0)).reg .rsp = some (.ptr 0 72) ∧
    (∀ t < 8, findWrite 2 t (after b5 (after b4 S0)).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b5 (after b4 S0)).mem, (w.r = 2 ∧ w.off + w.n ≤ 24) ∨ (w.r = 0 ∧ w.off + w.n ≤ 64)) := by
  decide +kernel
public theorem exit_a : exec b5 (after b4 S0) = some (after b5 (after b4 S0), .ret (.load 0 64 8)) :=
  run_b5a.trans (by rw [after_eq run_b5a])
/-- `stream_element`'s `None`: the tag `0` stored, the epilogue. -/
public theorem ok_b : EpiOk 64 slots (after b5 (after b4 M2)) = true ∧
    (∀ t < 8, findWrite 2 t (after b5 (after b4 M2)).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b5 (after b4 M2)).mem, w.r = 2 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel
/-- An element: the cursor advanced, the element copied with the tag `1`, the epilogue. -/
public theorem ok_c : EpiOk 64 slots (after b5 (after b3 M2)) = true ∧
    (∀ t < 8, findWrite 2 t (after b5 (after b3 M2)).mem = some (.lit 1, t)) ∧
    (∀ t < 8, findWrite 2 (8 + t) (after b5 (after b3 M2)).mem = some (.load 0 24 8, t)) ∧
    (∀ t < 8, findWrite 2 (16 + t) (after b5 (after b3 M2)).mem = some (.load 0 32 8, t)) ∧
    (∀ t < 8, findWrite 1 (352 + t) (after b5 (after b3 M2)).mem =
      some (.bin .add .W64 (.reg .r14) (.lit 1), t)) ∧
    (∀ w ∈ (after b5 (after b3 M2)).mem, (w.r = 1 ∧ 352 ≤ w.off ∧ w.off + w.n ≤ 360) ∨
      (w.r = 2 ∧ w.off + w.n ≤ 24)) := by
  decide +kernel

end NativeRustcVmX64.Transcript.NextScalar
