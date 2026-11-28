module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.Verify
public meta import NativeRustcVmX64.Code.Vm.Verify
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `verify`'s blocks, run by the symbolic executor (x86-64)

Region 0 the frame: the 816 bytes below the entry's RSP and the return address (RBP, R15, R14,
R13, R12, RBX pushed at offsets `808` to `768`; RSP at offset `8` in the body, the `TState` from
offset `8`, a callee's return address at `0`). `entryS` at the entry (`b0`: the prologue, `seed`'s
arguments); `initS` after `seed` and at `b3`, region 1 the `Decoded` at RBX (`b1`: `TState::new`'s
fields, `verify_execution`'s arguments; `b3`: the cursor, the area's length tested); `areaS` at `b4`,
region 2 the decoded area's first word (the stream's count, through the `Decoded`'s pointer);
`bodyS` elsewhere (`b2`: the walk's verdict tested; `b5`: the phase, `call phase_count`; `b6`: the
verdict; `b8`: `0`; `b9`: the epilogue). `b7` (an empty area's stream count) is never reached: the
area holds at least one word.
-/

namespace NativeRustcVmX64.Top.Verify

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.Verify NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(808, .rbp), (800, .r15), (792, .r14), (784, .r13), (776, .r12), (768, .rbx)]

def entryS : SState := init [824] [(.rsp, .ptr 0 816)]
def initS : SState := init [824, 24] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def bodyS : SState := init [824] [(.rsp, .ptr 0 8)]
def areaS : SState := init [824, 24, 8] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
  (aliases := [(.load 1 0 8, 2, 0)])

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 initS
sym_block run_b2 := exec b2 bodyS
sym_block run_b3 := exec b3 initS
sym_block run_b4 := exec b4 areaS
sym_block run_b5 := exec b5 bodyS
sym_block run_b6 := exec b6 bodyS
sym_block run_b8 := exec b8 bodyS
sym_block run_b9 := exec b9 bodyS

public theorem ok_b0 : ProOk 816 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 816) ∧
    (after b0 entryS).reg .rdi = some (.ptr 0 8) ∧ (after b0 entryS).reg .rsi = some (.reg .rdi) ∧
    (after b0 entryS).reg .rdx = some (.reg .rsi) ∧ (after b0 entryS).reg .rcx = some (.reg .rdx) ∧
    (after b0 entryS).reg .rbx = some (.reg .rcx) ∧ (after b0 entryS).reg .rbp = some (.ptr 0 8) ∧
    (after b0 entryS).reg .r12 = some (.reg .rsi) ∧ (after b0 entryS).reg .r13 = some (.reg .rdi) ∧
    (after b0 entryS).reg .r14 = some (.reg .r8) ∧ (after b0 entryS).reg .r15 = some (.reg .rdx) := by
  decide +kernel

/-- The frame's offsets `b1` zeroes: the sponge's `n_pending` and ground tag on, then the cursor,
the phase and the roots. -/
public theorem ok_b1 : MidOk 816 0 slots (after b1 initS) = true ∧
    (∀ w ∈ (after b1 initS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ 208 ≤ w.off ∧ w.off + w.n ≤ 768)) ∧
    (∀ i < 14, ∀ j < 8, findWrite 0 (208 + 8 * i + j) (after b1 initS).mem = some (.lit 0, j)) ∧
    (∀ i < 51, ∀ j < 8, findWrite 0 (360 + 8 * i + j) (after b1 initS).mem = some (.lit 0, j)) ∧
    (∀ j < 8, findWrite 0 (336 + j) (after b1 initS).mem = some (.load 1 0 8, j)) ∧
    (∀ j < 8, findWrite 0 (344 + j) (after b1 initS).mem = some (.load 1 8 8, j)) ∧
    (∀ j < 8, findWrite 0 (352 + j) (after b1 initS).mem = some (.load 1 16 8, j)) := by
  decide +kernel

public theorem regs_b1 : (after b1 initS).reg .rdi = some (.reg .rbp) ∧ (after b1 initS).reg .rsi = some (.reg .r13) ∧
    (after b1 initS).reg .rdx = some (.reg .r12) ∧ (after b1 initS).reg .rcx = some (.reg .r15) ∧
    (after b1 initS).reg .r8 = some (.reg .r14) ∧ (after b1 initS).reg .rbx = some (.ptr 1 0) ∧
    (after b1 initS).reg .rbp = some (.reg .rbp) ∧ (after b1 initS).reg .r12 = some (.reg .r12) ∧
    (after b1 initS).reg .r13 = some (.reg .r13) ∧ (after b1 initS).reg .r14 = some (.reg .r14) ∧
    (after b1 initS).reg .r15 = some (.reg .r15) := by
  decide +kernel

public theorem ok_b2 : MidOk 816 8 slots (after b2 bodyS) = true ∧ (after b2 bodyS).mem = [] ∧
    (after b2 bodyS).reg .rbx = some (.reg .rbx) := by
  decide +kernel

public theorem ok_b3 : MidOk 816 8 slots (after b3 initS) = true ∧ (after b3 initS).mem = [] ∧
    (after b3 initS).reg .rax = some (.load 0 360 8) ∧
    (after b3 initS).reg .rbx = some (.ptr 1 0) := by
  decide +kernel

public theorem ok_b4 : MidOk 816 8 slots (after b4 areaS) = true ∧ (after b4 areaS).mem = [] ∧
    (after b4 areaS).reg .rbx = some (.ptr 1 0) := by
  decide +kernel

public theorem ok_b5 : MidOk 816 0 slots (after b5 bodyS) = true ∧
    (∀ w ∈ (after b5 bodyS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b5 bodyS).reg .rdi = some (.reg .rbx) ∧
    (after b5 bodyS).reg .r14 = some (.load 0 368 8) := by
  decide +kernel

public theorem ok_b6 : MidOk 816 8 slots (after b6 bodyS) = true ∧ (after b6 bodyS).mem = [] ∧
    (after b6 bodyS).reg .rax = some (.bin .merge .W8 (.reg .rax)
      (.ite (.cmp .eq .W64 (.reg .r14) (.reg .rax)) (.lit 1) (.lit 0))) := by
  decide +kernel

public theorem ok_b8 : MidOk 816 8 slots (after b8 bodyS) = true ∧ (after b8 bodyS).mem = [] ∧
    (after b8 bodyS).reg .rax = some (.lit 0) := by
  decide +kernel

public theorem ok_b9 : EpiOk 816 slots (after b9 bodyS) = true ∧ (after b9 bodyS).mem = [] ∧
    (after b9 bodyS).reg .rax = some (.reg .rax) := by
  decide +kernel

end NativeRustcVmX64.Top.Verify
