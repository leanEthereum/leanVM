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
theorem walk_307 : CutsKnown 307 := os_cutsKnown lpTab_ok osOk_307

/-- `open_stacked__L1`. -/
theorem walk_308 : CutsKnown 308 := os_cutsKnown lpTab_ok osOk_308

/-- `open_stacked__L2`. -/
theorem walk_309 : CutsKnown 309 := os_cutsKnown lpTab_ok osOk_309

/-- `open_stacked__L3`. -/
theorem walk_310 : CutsKnown 310 := os_cutsKnown lpTab_ok osOk_310

end
end LeanVM.Guest.End
