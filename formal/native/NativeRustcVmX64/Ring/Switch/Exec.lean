module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.RingSwitch
public import NativeRustcVmX64.Code.Vm.RingSwitch.Names
public meta import NativeRustcVmX64.Code.Vm.RingSwitch
public meta import NativeRustcVmX64.Transcript.Frame

/-!
# `ring_switch`'s blocks, run by the symbolic executor (x86-64)

Region 0 the 432-byte frame (RBP, R15, R14, R12, RBX pushed at offsets `424` to `392`, the 16
challenges from `8`, `g`'s copy from `264`, a callee's return address at `0`) and the return
address, region 1 the `RingW` output. From `entryS`: `b0` (the prologue, `call grind`); from `gS`
(after it: RSP at offset `8`, the output in RBX): `b1` (its `Option<()>`), then `b6` (`None`) or
`b2` (the challenges zeroed, `call sample_challenges` into them); from `cS` (R15 the challenges):
`b3` (`g` copied, `call ring_coefficients`); from `tS` (R12 `g`'s copy): `b4` (`call
ring_target`); from `eS`: `b5`, `b6` (the target stored, AL the grind's, the epilogue).
-/

namespace NativeRustcVmX64.Ring.Switch

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.RingSwitch NativeRustcVmX64.Transcript

@[expose] public section

/-- The frame's slots. -/
def slots : Slots := [(424, .rbp), (416, .r15), (408, .r14), (400, .r12), (392, .rbx)]

def entryS : SState := init [440, 1040] [(.rsp, .ptr 0 432), (.rdx, .ptr 1 0)]
def gS : SState := init [440, 1040] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0)]
def G1 : SState := after b1 gS
def cS : SState := init [440, 1040] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r15, .ptr 0 8)]
def tS : SState :=
  init [440, 1040] [(.rsp, .ptr 0 8), (.rbx, .ptr 1 0), (.r15, .ptr 0 8), (.r12, .ptr 0 264)]

end

set_option Elab.async false

sym_block run_b0 := exec b0 entryS
sym_block run_b1 := exec b1 gS
sym_block run_b6n := exec b6 G1
sym_block run_b2 := exec b2 G1
sym_block run_b3 := exec b3 cS
sym_block run_b4 := exec b4 tS
sym_block run_b5 := exec b5 gS
sym_block run_b6s := exec b6 (after b5 gS)

public theorem ok_b0 : ProOk 432 0 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 432) ∧
    (after b0 entryS).reg .rsi = some (.lit 13) ∧ (after b0 entryS).reg .rbx = some (.ptr 1 0) ∧
    (after b0 entryS).reg .r12 = some (.reg .rdi) ∧ (after b0 entryS).reg .r14 = some (.reg .rsi) ∧
    (after b0 entryS).reg .rdi = some (.reg .rdi) := by
  decide +kernel

public theorem exit_b1 : exec b1 gS = some (G1, .cond (SBool.cmp .eq .W8
    (.bin .and .W8 (.reg .rax) (.reg .rax)) (.lit 0)) NativeRustcVmX64.Vm.RingSwitch.label_2) :=
  run_b1.trans (by rw [show G1 = _ from after_eq run_b1])

/-- `None`: the epilogue, AL the grind's. -/
public theorem ok_n : EpiOk 432 slots (after b6 G1) = true ∧ (after b6 G1).mem = [] ∧
    (after b6 G1).reg .rax = some (.reg .rax) := by
  decide +kernel

/-- The challenges zeroed, `sample_challenges` called on them. -/
public theorem ok_b2 : MidOk 432 0 slots (after b2 G1) = true ∧
    (∀ w ∈ (after b2 G1).mem, w.r = 0 ∧ w.off + w.n ≤ 264) ∧
    (after b2 G1).reg .rdi = some (.reg .r12) ∧ (after b2 G1).reg .rsi = some (.ptr 0 8) ∧
    (after b2 G1).reg .rdx = some (.lit 16) ∧ (after b2 G1).reg .rbx = some (.ptr 1 0) ∧
    (after b2 G1).reg .rbp = some (.un .trunc .W32 (.reg .rax)) ∧
    (after b2 G1).reg .r14 = some (.reg .r14) ∧ (after b2 G1).reg .r15 = some (.ptr 0 8) := by
  decide +kernel

/-- `g` copied, `ring_coefficients` called on `f`, the copy, the `RingW`'s coefficients. -/
public theorem ok_b3 : MidOk 432 0 slots (after b3 cS) = true ∧
    (∀ w ∈ (after b3 cS).mem, w.r = 0 ∧ (w.off + w.n ≤ 8 ∨ (264 ≤ w.off ∧ w.off + w.n ≤ 392))) ∧
    (∀ j < 16, ∀ t < 8, findWrite 0 (264 + 8 * j + t) (after b3 cS).mem =
      some (.load 0 (136 + 8 * j) 8, t)) ∧
    (after b3 cS).reg .rdi = some (.ptr 0 8) ∧ (after b3 cS).reg .rsi = some (.ptr 0 264) ∧
    (after b3 cS).reg .rdx = some (.ptr 1 16) ∧ (after b3 cS).reg .rbx = some (.ptr 1 0) ∧
    (after b3 cS).reg .r12 = some (.ptr 0 264) ∧ (after b3 cS).reg .r15 = some (.ptr 0 8) ∧
    (after b3 cS).reg .r14 = some (.reg .r14) ∧ (after b3 cS).reg .rbp = some (.reg .rbp) := by
  decide +kernel

public theorem ok_b4 : MidOk 432 0 slots (after b4 tS) = true ∧
    (∀ w ∈ (after b4 tS).mem, w.r = 0 ∧ w.off + w.n ≤ 8) ∧
    (after b4 tS).reg .rdi = some (.reg .r14) ∧ (after b4 tS).reg .rsi = some (.ptr 0 8) ∧
    (after b4 tS).reg .rdx = some (.ptr 0 264) ∧ (after b4 tS).reg .rbx = some (.ptr 1 0) ∧
    (after b4 tS).reg .rbp = some (.reg .rbp) := by
  decide +kernel

/-- The target stored, AL the grind's (in EBP), the epilogue. -/
public theorem ok_s : EpiOk 432 slots (after b6 (after b5 gS)) = true ∧
    (∀ t < 8, findWrite 1 t (after b6 (after b5 gS)).mem = some (.reg .rax, t)) ∧
    (∀ t < 8, findWrite 1 (8 + t) (after b6 (after b5 gS)).mem = some (.reg .rdx, t)) ∧
    (∀ w ∈ (after b6 (after b5 gS)).mem, w.r = 1 ∧ 0 ≤ w.off ∧ w.off + w.n ≤ 16) ∧
    (after b6 (after b5 gS)).reg .rax = some (.un .trunc .W32 (.reg .rbp)) := by
  decide +kernel

end NativeRustcVmX64.Ring.Switch
