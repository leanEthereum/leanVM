module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.TStateReadScalar
public import NativeRustcVmX64.Code.Vm.TStateReadScalar.Names
public meta import NativeRustcVmX64.Code.Vm.TStateReadScalar
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `TState::read_scalar`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 80-byte frame (R15 to RBX pushed at offsets `72` to `40`, `next_scalar`'s output at
`16`, the calls' return addresses at `0`) and the return address, region 1 the output. `entryS` at
the entry (`b0`: the prologue, `call next_scalar`); `tagS` after it: `b1` tests the output's tag,
then `b4`, `b5` (`None`: the tag `0` stored, the epilogue) or `b2` (`call absorb` with the
element and the tag `1`); `storeS` after `absorb`: `b3`, `b5` (the element and the tag stored, the
epilogue).
-/

namespace NativeRustcVmX64.Transcript.ReadScalar

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.TStateReadScalar

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(72, .r15), (64, .r14), (56, .r13), (48, .r12), (40, .rbx)]

def entryS : SState := init [88] [(.rsp, .ptr 0 80)]
def tagS : SState := init [88, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def T1 : SState := after b1 tagS
def storeS : SState := init [88, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 tagS
sym_block run_b2 := exec b2 T1
sym_block run_b4 := exec b4 T1
sym_block run_b5n := exec b5 (after b4 T1)
sym_block run_b3 := exec b3 storeS
sym_block run_b5s := exec b5 (after b3 storeS)

public theorem ok_b0 : ProOk 80 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 80) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 16) ∧ (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .r14 = some (.reg .rsi) ∧ (after b0 entryS).reg .rbx = some (.reg .rdi) := by
  decide +kernel
public theorem exit_b1 : exec b1 tagS = some (T1,
    .cond (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.TStateReadScalar.label_2) :=
  run_b1.trans (by rw [show T1 = _ from after_eq run_b1])
public theorem ok_b2 : MidOk 80 0 slots (after b2 T1) = true ∧
    (∀ w ∈ (after b2 T1).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b2 T1).reg .rdi = some (.reg .r14) ∧ (after b2 T1).reg .rsi = some (.load 0 24 8) ∧
    (after b2 T1).reg .rdx = some (.load 0 32 8) ∧ (after b2 T1).reg .rcx = some (.lit 1) ∧
    (after b2 T1).reg .r13 = some (.lit 1) ∧ (after b2 T1).reg .r15 = some (.load 0 24 8) ∧
    (after b2 T1).reg .r12 = some (.load 0 32 8) ∧ (after b2 T1).reg .rbx = some (.ptr 1 0) ∧
    (after b2 T1).reg .r14 = some (.reg .r14) := by
  decide +kernel
public theorem ok_none : EpiOk 80 slots (after b5 (after b4 T1)) = true ∧
    (∀ t < 8, findWrite 1 t (after b5 (after b4 T1)).mem = some (.lit 0, t)) ∧
    (∀ w ∈ (after b5 (after b4 T1)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel
public theorem ok_some : EpiOk 80 slots (after b5 (after b3 storeS)) = true ∧
    (∀ t < 8, findWrite 1 t (after b5 (after b3 storeS)).mem = some (.reg .r13, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b5 (after b3 storeS)).mem = some (.reg .r15, t)) ∧
    (∀ t < 8, findWrite 1 (16 + t) (after b5 (after b3 storeS)).mem = some (.reg .r12, t)) ∧
    (∀ w ∈ (after b5 (after b3 storeS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 24) := by
  decide +kernel

end NativeRustcVmX64.Transcript.ReadScalar
