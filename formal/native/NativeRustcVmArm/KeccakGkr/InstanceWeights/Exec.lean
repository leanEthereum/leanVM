module

public import NativeRustcVmArm.Code.Vm.InstanceWeights.Names
public import NativeRustcArm.Sym
public import NativeRustcVmArm.Code.Vm.InstanceWeights
public import NativeRustcVmArm.KeccakGkr.InstanceWeights.Mask
public meta import NativeRustcVmArm.Code.Vm.InstanceWeights
public meta import NativeRustcVmArm.KeccakGkr.InstanceWeights.Mask
import Mathlib.Tactic.IntervalCases

/-!
# `instance_weights`' blocks, run by the symbolic executor

Region 0 the 976-byte frame throughout. The prologue (`b0`, up to the call of `powers`) from the
entry; after the call, `b1`, the fourteen turns of the loop (`b2`, its control flow constant: the
loop counter is a literal) and the tail (`b3`, up to the call of `memcpy`) in one environment
(`it`); the epilogue (`b4`). What the tail leaves in the frame's `Buf` passes `itemsOk`.
-/

namespace NativeRustcVmArm.KeccakGkr.InstanceWeights

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.InstanceWeights
open NativeRustcVmArm.Arrays NativeRustcVmArm.Sumcheck

@[expose] public section

/-- The entry: region 0 the frame below SP. -/
def entryS : SState := init [(976, true)] (.ptr 0 976)
/-- The body: region 0 the frame from SP. -/
def bodyS : SState := init [(976, true)] (.ptr 0 0)
/-- After `b1` and `n` turns of the loop. -/
def it : Nat → SState
  | 0 => after b1 bodyS
  | n + 1 => after b2 (it n)

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
sym_block e4 := exec b4 bodyS

public section

theorem it_zero : it 0 = after b1 bodyS := rfl

/-- **A turn of the loop**: back at the head but after the last. -/
theorem loop_exec {j : Nat} (hj : j < 14) :
    exec b2 (it j) = some (it (j + 1), .cond (.lit (j != 13)) NativeRustcVmArm.Vm.InstanceWeights.label_1) := by
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

/-- The tail leaves the `Buf` `itemsOk` checks, and writes only the frame's locals. -/
theorem tail_ok : itemsOk (after b3 (it 14)).mem = true ∧
    ∀ w ∈ (after b3 (it 14)).mem, w.r = 0 ∧ w.off + w.n ≤ 880 := by
  rw [after_eq e3]
  decide +kernel

end

end NativeRustcVmArm.KeccakGkr.InstanceWeights
