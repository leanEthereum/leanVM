/-
  LeanVM.Guest.WalkOs3

  The cut obligations (`CutsKnown`) of `open_stacked__L12`
  (`os_cutsKnown`, `WalkOsOk3.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsTabOk
public import LeanVM.Guest.WalkOsOk3

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L12`. -/
theorem walk_323 : CutsKnown 323 := os_cutsKnown lpTab_ok osOk_323

end
end LeanVM.Guest.End
