/-
  LeanVM.Guest.WalkOs2

  The cut obligations (`CutsKnown`) of `open_stacked__L8`, `open_stacked__L9`, `open_stacked__L10`, `open_stacked__L11`
  (`os_cutsKnown`, `WalkOsOk2.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsTabOk
public import LeanVM.Guest.WalkOsOk2

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L8`. -/
theorem walk_319 : CutsKnown 319 := os_cutsKnown lpTab_ok osOk_319

/-- `open_stacked__L9`. -/
theorem walk_320 : CutsKnown 320 := os_cutsKnown lpTab_ok osOk_320

/-- `open_stacked__L10`. -/
theorem walk_321 : CutsKnown 321 := os_cutsKnown lpTab_ok osOk_321

/-- `open_stacked__L11`. -/
theorem walk_322 : CutsKnown 322 := os_cutsKnown lpTab_ok osOk_322

end
end LeanVM.Guest.End
