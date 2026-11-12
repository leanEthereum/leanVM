/-
  LeanVM.Guest.WalkOs2

  The cut obligations (`CutsKnown`) of `open_stacked__L6`, `open_stacked__L7`, `open_stacked__L8` (`os_cutsKnown`, `WalkOsOk2.lean`'s
  checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsOk2

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L6`. -/
theorem walk_342 : CutsKnown 342 := os_cutsKnown osOk_342

/-- `open_stacked__L7`. -/
theorem walk_343 : CutsKnown 343 := os_cutsKnown osOk_343

/-- `open_stacked__L8`. -/
theorem walk_344 : CutsKnown 344 := os_cutsKnown osOk_344

end
end LeanVM.Guest.End
