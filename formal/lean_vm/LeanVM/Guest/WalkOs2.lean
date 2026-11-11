/-
  LeanVM.Guest.WalkOs2

  The cut obligations (`CutsKnown`) of `open_stacked__L8`, `open_stacked__L9`, `open_stacked__L10`
  (`os_cutsKnown`, `WalkOsOk2.lean`'s checks).
-/

module

public import LeanVM.Guest.WalkOs
public import LeanVM.Guest.WalkOsTabOk
public import LeanVM.Guest.WalkOsOk2

namespace LeanVM.Guest.End

@[expose] public section

/-- `open_stacked__L8`. -/
theorem walk_315 : CutsKnown 315 := os_cutsKnown lpTab_ok osOk_315

/-- `open_stacked__L9`. -/
theorem walk_316 : CutsKnown 316 := os_cutsKnown lpTab_ok osOk_316

/-- `open_stacked__L10`. -/
theorem walk_317 : CutsKnown 317 := os_cutsKnown lpTab_ok osOk_317

end
end LeanVM.Guest.End
