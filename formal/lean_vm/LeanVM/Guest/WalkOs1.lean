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
theorem walk_315 : CutsKnown 315 := os_cutsKnown lpTab_ok osOk_315

/-- `open_stacked__L5`. -/
theorem walk_316 : CutsKnown 316 := os_cutsKnown lpTab_ok osOk_316

/-- `open_stacked__L6`. -/
theorem walk_317 : CutsKnown 317 := os_cutsKnown lpTab_ok osOk_317

/-- `open_stacked__L7`. -/
theorem walk_318 : CutsKnown 318 := os_cutsKnown lpTab_ok osOk_318

end
end LeanVM.Guest.End
