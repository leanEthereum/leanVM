module

public import NativeRustcVmX64.Transcript.Frame
public import NativeRustcVmX64.Code.Vm.InstanceWeights
public import NativeRustcVmX64.KeccakGkr.InstanceWeights.Mask
public meta import NativeRustcVmX64.Code.Vm.InstanceWeights
public meta import NativeRustcVmX64.Transcript.Frame
public meta import NativeRustcVmX64.KeccakGkr.InstanceWeights.Mask
import Mathlib.Tactic.IntervalCases
public import NativeRustcVmX64.Code.Vm.InstanceWeights.Names
public import NativeRustcVmX64.Code.Vm.Memcpy.Names
public import NativeRustcVmX64.Code.Vm.Powers.Names

/-!
# `instance_weights`' blocks, run by the symbolic executor (x86-64)

Region 0 the 1048-byte frame and the return address: the six pushes (offsets `1000` to `1040`),
the 984 bytes of locals from offset `16` (RSP's in the body), below them the 8-byte slot a call
pushes its return address in (offset `8`) and eight unused bytes. Region 1 in the body is the
read-only `memcpy` GOT slot. The prologue (`b0`, up to the call of `powers`) from the entry; after the call, `b1`,
the fourteen turns of the loop (`b2`, its control flow constant: the loop counter is a literal)
and the tail (`b3`, up to the call of `memcpy`) in one environment (`it`); the epilogue (`b4`).
-/

namespace NativeRustcVmX64.KeccakGkr.InstanceWeights

open NativeRustcX64 NativeRustcX64.Sym NativeRustcVmX64.Vm.InstanceWeights
open NativeRustcVmX64.Transcript

@[expose] public section

/-- The entry: region 0 the frame below RSP and the return address. -/
def entryS : SState := init [1056] [(.rsp, .ptr 0 1048)]
/-- The body: RSP at offset `16`, with the ordinary-memory `memcpy` slot. -/
def bodyS : SState :=
  (init [1056, 8] [(.rsp, .ptr 0 16)]
    (aliases := [(.gotSlot "memcpy", 1, 0)])).withKnownBytes 1 0 8 (.label "memcpy")

/-- The epilogue reads only its frame. -/
def exitS : SState := init [1056] [(.rsp, .ptr 0 16)]
/-- After `b1` and `n` turns of the loop. -/
def it : Nat → SState
  | 0 => after b1 bodyS
  | n + 1 => after b2 (it n)

/-- The pushed registers' slots. -/
def slots : Slots :=
  [(1040, .rbp), (1032, .r15), (1024, .r14), (1016, .r13), (1008, .r12), (1000, .rbx)]

end

set_option Elab.async false

sym_block e0 := exec b0 entryS
sym_block e1 := exec b1 bodyS
sym_block l0 := exec b2 (it 0)
sym_block l1 := exec b2 (it 1)
sym_block l2 := exec b2 (it 2)
sym_block l3 := exec b2 (it 3)
sym_block l4 := exec b2 (it 4)
sym_block l5 := exec b2 (it 5)
sym_block l6 := exec b2 (it 6)
sym_block l7 := exec b2 (it 7)
sym_block l8 := exec b2 (it 8)
sym_block l9 := exec b2 (it 9)
sym_block l10 := exec b2 (it 10)
sym_block l11 := exec b2 (it 11)
sym_block l12 := exec b2 (it 12)
sym_block l13 := exec b2 (it 13)
sym_block e3 := exec b3 (it 14)
sym_block e4 := exec b4 exitS

public section

theorem it_zero : it 0 = after b1 bodyS := rfl

theorem b2_ne : b2 ≠ [] := List.ne_nil_of_length_pos (by rw [b2_length]; decide)

/-- The prologue: the slots pushed, the result's address saved at `512`, `powers`' arguments. -/
theorem ok_b0 : ProOk 1048 8 slots (after b0 entryS) = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 1048) ∧
    (∀ i < 8, findWrite 0 (512 + i) (after b0 entryS).mem = some (.reg .rdi, i)) ∧
    (after b0 entryS).reg .rdi = some (.reg .rsi) ∧ (after b0 entryS).reg .rsi = some (.reg .rdx) ∧
    (after b0 entryS).reg .rdx = some (.ptr 0 112) ∧ (after b0 entryS).reg .rcx = some (.lit 24) := by
  rw [after_eq e0]
  decide +kernel

theorem exit_b0 : exec b0 entryS =
    some (after b0 entryS, .call NativeRustcVmX64.Vm.Powers.entryLabel) :=
  e0.trans (by rw [after_eq e0])

theorem exit_b1 : exec b1 bodyS = some (it 0, .fall) := e1.trans (by rw [it_zero, after_eq e1])

/-- **A turn of the loop**: back at the head but after the last. -/
theorem loop_exec {j : Nat} (hj : j < 14) :
    exec b2 (it j) = some (it (j + 1), .cond (.lit (j != 13)) NativeRustcVmX64.Vm.InstanceWeights.label_1) := by
  show exec b2 (it j) = some (after b2 (it j), _)
  interval_cases j
  · rw [after_eq l0]; exact l0
  · rw [after_eq l1]; exact l1
  · rw [after_eq l2]; exact l2
  · rw [after_eq l3]; exact l3
  · rw [after_eq l4]; exact l4
  · rw [after_eq l5]; exact l5
  · rw [after_eq l6]; exact l6
  · rw [after_eq l7]; exact l7
  · rw [after_eq l8]; exact l8
  · rw [after_eq l9]; exact l9
  · rw [after_eq l10]; exact l10
  · rw [after_eq l11]; exact l11
  · rw [after_eq l12]; exact l12
  · rw [after_eq l13]; exact l13

theorem exit_b3 : exec b3 (it 14) = some (after b3 (it 14), .call NativeRustcVmX64.Vm.Memcpy.entryLabel) :=
  e3.trans (by rw [after_eq e3])

/-- The tail leaves the `Buf` `itemsOk` checks, writes only the frame's locals and calls `memcpy`
from the `Buf` to the result. -/
theorem ok_b3 : MidOk 1048 8 slots (after b3 (it 14)) = true ∧ itemsOk (after b3 (it 14)).mem = true ∧
    (∀ w ∈ (after b3 (it 14)).mem, w.r = 0 ∧ w.off + w.n ≤ 1000) ∧
    (after b3 (it 14)).reg .rdi = some (.load 0 512 8) ∧
    (after b3 (it 14)).reg .rsi = some (.ptr 0 736) ∧ (after b3 (it 14)).reg .rdx = some (.lit 264) := by
  rw [after_eq e3]
  decide +kernel

theorem exit_b4 : exec b4 exitS = some (after b4 exitS, .ret (.load 0 1048 8)) :=
  e4.trans (by rw [after_eq e4])

theorem ok_b4 : EpiOk 1048 slots (after b4 exitS) = true ∧ (after b4 exitS).mem = [] := by
  rw [after_eq e4]
  decide +kernel

end

end NativeRustcVmX64.KeccakGkr.InstanceWeights
