/-
  LeanVM.Guest.WalkOs1

  The cut obligations (`CutsKnown`) of `open_stacked__L3`, `open_stacked__L4`, `open_stacked__L5` (`os_cutsKnown`, `WalkOsOk1.lean`'s
  checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk1

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L3`. -/
theorem walk_339 : CutsKnown 339 := os_cutsKnown osOk_339

/-- `open_stacked__L4`. -/
theorem walk_340 : CutsKnown 340 := os_cutsKnown osOk_340

/-- `open_stacked__L5`. -/
theorem walk_341 : CutsKnown 341 := os_cutsKnown osOk_341

end
end LeanVM.Guest.End
