module

public import NativeRustcVmArm.Whir.FinalLevel.Basic

/-!
# `final_level`'s blocks: what they write

Decided facts on the blocks' final states (`after`): the slots and the frame writes of the entry
(`ok_e4`).
-/

namespace NativeRustcVmArm.Whir.FinalLevel

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Ring NativeRustcVmArm.Vm.FinalLevel

public section

theorem ok_e4 : slotsOk (after b4 (after b1 (after b0 entryS))) slots = true ∧
    ∀ w ∈ (after b4 (after b1 (after b0 entryS))).mem, w.r = 0 ∧ w.off + w.n ≤ 2672 := by
  rw [after_eq run_b4e]; decide +kernel

end

end NativeRustcVmArm.Whir.FinalLevel
