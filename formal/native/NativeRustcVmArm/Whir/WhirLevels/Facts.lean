module

public import NativeRustcVmArm.Whir.WhirLevels.Steps
public import NativeRustcVmArm.Whir.WhirLevels.Stages
public meta import NativeRustcVmArm.Whir.WhirLevels.Exec

/-!
# `whir_levels`: the literal blocks pass their checks

Each check by `decide +kernel` on the block's literal end state (`after`).
-/

namespace NativeRustcVmArm.Whir.WhirLevels

open NativeRustcArm NativeRustcArm.Sym NativeRustcVmArm.Vm.WhirLevels NativeRustcVmArm.Whir
open NativeRustcVmArm.Ring

set_option Elab.async false

public theorem ok_b0 : slotsOk (after b0 entryS) slots = true ∧
    (∀ w ∈ (after b0 entryS).mem, w.r = 0 ∧ w.off + w.n ≤ 96) ∧
    (after b0 entryS).sp = .ptr 0 0 ∧ (after b0 entryS).reg .X29 = some (.reg .X29) := by
  decide +kernel

public theorem ok_b7 : FoldOk 1 32 (after b7 (lvS 32)) = true := by decide +kernel
public theorem ok_b14 : FoldOk 2 56 (after b14 (lvS 56)) = true := by decide +kernel
public theorem ok_b21 : FoldOk 3 80 (after b21 (lvS 80)) = true := by decide +kernel
public theorem ok_b27 : FoldOk 4 104 (after b27 (lvS 104)) = true := by decide +kernel
public theorem ok_b33 : FoldOk 5 128 (after b33 (lvS 128)) = true := by decide +kernel
public theorem ok_b3 : WOk (after b3 wS) = true := by decide +kernel
public theorem ok_b9 : WOk (after b9 wS) = true := by decide +kernel
public theorem ok_b16 : WOk (after b16 wS) = true ∧
    (after b16 wS).reg .X8 = some (.bin .add .W64 (.reg .X23) (.lit 48)) := by decide +kernel
public theorem ok_b23 : WOk (after b23 wS) = true ∧
    (after b23 wS).reg .X8 = some (.bin .add .W64 (.reg .X23) (.lit 72)) := by decide +kernel
public theorem ok_b29 : WOk (after b29 wS) = true ∧
    (after b29 wS).reg .X8 = some (.bin .add .W64 (.reg .X23) (.lit 96)) := by decide +kernel
public theorem ok_b35 : WOk (after b35 wS) = true := by decide +kernel
public theorem ok_b5 : NextOk 0 40 (.ptr 0 0) (after b5 (lvS 40)) = true := by decide +kernel
public theorem ok_b11 : NextOk 1 64 (.reg .X27) (after b11 (lvS 64)) = true := by decide +kernel
public theorem ok_b18 : NextOk 2 88 (.ptr 0 48) (after b18 (lvS 88)) = true := by decide +kernel
public theorem ok_b24 : NextOk 3 112 (.ptr 0 72) (after b24 (lvS 112)) = true := by decide +kernel
public theorem ok_b30 : NextOk 4 136 (.ptr 0 96) (after b30 (lvS 136)) = true := by decide +kernel
public theorem ok_b12 : RegsOk (after b12 regsS) = true := by decide +kernel
public theorem ok_b19 : RegsOk (after b19 regsS) = true := by decide +kernel
public theorem ok_b25 : RegsOk (after b25 regsS) = true := by decide +kernel
public theorem ok_b31 : RegsOk (after b31 regsS) = true := by decide +kernel
public theorem ok_b17 : JumpOk (.reg .X8) (after b17 regsS) = true := by decide +kernel
public theorem ok_b36 : JumpOk (.reg .X26) (after b36 regsS) = true := by decide +kernel
public theorem b2_eq : b8 = b2 ∧ b15 = b2 ∧ b22 = b2 ∧ b28 = b2 ∧ b34 = b2 ∧ b6 = b2 ∧ b13 = b2 ∧
    b20 = b2 ∧ b26 = b2 ∧ b32 = b2 := by decide +kernel

end NativeRustcVmArm.Whir.WhirLevels
