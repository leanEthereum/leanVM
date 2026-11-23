module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.CommitStack
public import NativeRustcVmX64.Code.Vm.CommitStack.Names
public import NativeRustcVmX64.Code.Vm.Ladder.Names
public import NativeRustcVmX64.Code.Vm.TStateReadCommitment.Names
public meta import NativeRustcVmX64.Code.Vm.CommitStack
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `commit_stack`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 192-byte frame and the return address (R14, RBX pushed at `184`, `176`; `ladder`'s
result at `16` to `176`; the call's return address at `0`). `entryS` at the entry (`b0`: the
prologue, RBX the `TState`, R14 `μ`, `call ladder` on the frame); `retS` from the return (`b1`: the
tag; `b2`: the count in `1..6`; `b3`: AL = `0`, the epilogue; `b4`: level `0`'s shape into RSI,
RDX, the registers restored, the tail call of `read_commitment`).
-/

namespace NativeRustcVmX64.Layout.CommitStack

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.CommitStack NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(184, .r14), (176, .rbx)]

def entryS : SState := init [200] [(.rsp, .ptr 0 192)]
def retS : SState := init [200] [(.rsp, .ptr 0 8)]
def S1 : SState := after b1 retS
def S2 : SState := after b2 S1

/-- `b4`'s height: `μ - fold`, saturating, plus the rate. -/
def heightSym : Sym :=
  .bin .add .W64 (.load 0 32 8)
    (.ite (SBool.cmp .ult .W64 (.reg .r14) (.load 0 24 8)).not
      (.bin .sub .W64 (.reg .r14) (.load 0 24 8)) (.lit 0))

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 retS
sym_block run_b2 := exec b2 S1
sym_block run_b3 := exec b3 S1
sym_block run_b4 := exec b4 S2

public theorem exit_b0 : exec b0 entryS = some (after b0 entryS,
    .call NativeRustcVmX64.Vm.Ladder.entryLabel) :=
  run_b0.trans (by rw [after_eq run_b0])
public theorem ok_b0 : ProOk 192 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 192) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 16) ∧ (after b0 entryS).reg .rsi = some (.reg .rsi) ∧
    (after b0 entryS).reg .rdx = some (.reg .rdx) ∧ (after b0 entryS).reg .rbx = some (.reg .rdi) ∧
    (after b0 entryS).reg .r14 = some (.reg .rsi) := by
  decide +kernel
public theorem exit_b1 : exec b1 retS = some (S1,
    .cond (SBool.cmp .eq .W32 (.load 0 16 4) (.lit 1)).not NativeRustcVmX64.Vm.CommitStack.label_2) :=
  run_b1.trans (by rw [show S1 = _ from after_eq run_b1])
public theorem ok_b1 : MidOk 192 8 slots S1 = true ∧ S1.mem = [] := by decide +kernel
public theorem exit_b2 : exec b2 S1 = some (S2,
    .cond (SBool.cmp .ult .W64 (.bin .add .W64 (.lit 18446744073709551609) (.load 0 168 8))
      (.lit 18446744073709551610)).not NativeRustcVmX64.Vm.CommitStack.label_3) :=
  run_b2.trans (by rw [show S2 = _ from after_eq run_b2])
public theorem ok_b2 : MidOk 192 8 slots S2 = true ∧ S2.mem = [] := by decide +kernel
public theorem exit_b3 : exec b3 S1 = some (after b3 S1, .ret (.load 0 192 8)) :=
  run_b3.trans (by rw [after_eq run_b3])
public theorem end_b3 : EpiOk 192 slots (after b3 S1) = true ∧ (after b3 S1).mem = [] ∧
    (after b3 S1).reg .rax = some (.lit 0) := by
  decide +kernel
public theorem exit_b4 : exec b4 S2 = some (after b4 S2,
    .jump NativeRustcVmX64.Vm.TStateReadCommitment.entryLabel) :=
  run_b4.trans (by rw [after_eq run_b4])
public theorem end_b4 : slotsLoaded slots (after b4 S2) = true ∧
    keepsOthers slots (after b4 S2) = true ∧ (after b4 S2).reg .rsp = some (.ptr 0 192) ∧
    (after b4 S2).mem = [] ∧ (after b4 S2).reg .rdi = some (.reg .rbx) ∧
    (after b4 S2).reg .rsi = some heightSym ∧
    (after b4 S2).reg .rdx = some (.bin .shl .W64 (.lit 1) (.load 0 24 8)) := by
  decide +kernel

end NativeRustcVmX64.Layout.CommitStack
