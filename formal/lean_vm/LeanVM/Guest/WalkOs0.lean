/-
  LeanVM.Guest.WalkOs0

  The cut obligations (`CutsKnown`) of `open_stacked__L0`, `open_stacked__L1`, `open_stacked__L2`, `open_stacked__L3`
  (`os_cutsKnown`, `WalkOsOk0.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsTabOk
public import LeanVM.Guest.WalkOsOk0

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L0`. -/
theorem walk_311 : CutsKnown 311 := os_cutsKnown lpTab_ok osOk_311

/-- `open_stacked__L1`. -/
theorem walk_312 : CutsKnown 312 := os_cutsKnown lpTab_ok osOk_312

/-- `open_stacked__L2`. -/
theorem walk_313 : CutsKnown 313 := os_cutsKnown lpTab_ok osOk_313

/-- `open_stacked__L3`. -/
theorem walk_314 : CutsKnown 314 := os_cutsKnown lpTab_ok osOk_314

end
end LeanVM.Guest.End
