/-
  LeanVM.Guest.WalkOs1

  The cut obligations (`CutsKnown`) of `open_stacked__L4`, `open_stacked__L5`, `open_stacked__L6`, `open_stacked__L7`
  (`os_cutsKnown`, `WalkOsOk1.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsTabOk
public import LeanVM.Guest.WalkOsOk1

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L4`. -/
theorem walk_311 : CutsKnown 311 := os_cutsKnown lpTab_ok osOk_311

/-- `open_stacked__L5`. -/
theorem walk_312 : CutsKnown 312 := os_cutsKnown lpTab_ok osOk_312

/-- `open_stacked__L6`. -/
theorem walk_313 : CutsKnown 313 := os_cutsKnown lpTab_ok osOk_313

/-- `open_stacked__L7`. -/
theorem walk_314 : CutsKnown 314 := os_cutsKnown lpTab_ok osOk_314

end
end LeanVM.Guest.End
