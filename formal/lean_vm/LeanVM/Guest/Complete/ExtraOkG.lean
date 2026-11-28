/-
  LeanVM.Guest.Complete.ExtraOkG

  The alignment's hint-only cells are fresh: `ExtraOk exA`, by the kernel.
-/

module

public import LeanVM.Guest.EndExecX
public import LeanVM.Guest.Memory.GuestExtra

/-!
# The alignment's hint-only cells

`exA` (the core route's `Bridge.alignExtras`) gives hint-only cells to one function only, compiled
function `99` (`log2_ceil_in_the_exponent__L16_L34`): `exA_only` checks every other index's list
empty, `extraOk_99` that function's cells fresh (`extraOkB`), both by the kernel. So
`extraOk_exA : ExtraOk exA`, what `refX_of_callAtA` needs to write the hint-only values into the
reference memory (`RefH.extra`).
-/

namespace LeanVM.Guest.Complete

open LeanVM.Guest LeanVM.Guest.Memory LeanVM.Guest.EndExec

public section

/-- Every compiled function but `99` has no hint-only cell. -/
theorem exA_only : (List.range nFns).all (fun j ↦ (exA j).isEmpty || j == 99) = true := by
  decide +kernel

/-- Compiled function `99`'s hint-only cells are fresh. -/
theorem extraOk_99 : extraOk exA 99 = true := by
  decide +kernel

/-- **The alignment's hint-only cells are fresh.** -/
theorem extraOk_exA : ExtraOk exA := by
  refine ⟨by decide +kernel, fun j hj ↦ ?_⟩
  have h := List.all_eq_true.mp exA_only j (List.mem_range.mpr hj)
  simp only [Bool.or_eq_true, List.isEmpty_iff, beq_iff_eq] at h
  rcases h with h | rfl
  · simp only [extraOk, extraOkB, h, List.isEmpty_nil, Bool.true_or]
  · exact extraOk_99

end

end LeanVM.Guest.Complete
