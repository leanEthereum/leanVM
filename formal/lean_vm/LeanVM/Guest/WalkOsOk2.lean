/-
  LeanVM.Guest.WalkOsOk2

  The certificates of `open_stacked__L6`, `open_stacked__L7`, `open_stacked__L8` assume the window table and hand on, at each level's dispatch into
  `level_queries`, the windows that level's `level_positions` dispatch decodes (`osOk`), by kernel
  evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

@[expose] public section

set_option maxRecDepth 100000 in
/-- `open_stacked__L6`. -/
theorem osOk_342 : osOk 342 [(79, 32), (175, 289), (271, 438), (367, 587), (441, 701)] = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `open_stacked__L7`. -/
theorem osOk_343 : osOk 343 [(79, 32), (175, 289), (271, 438), (367, 587), (441, 701)] = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `open_stacked__L8`. -/
theorem osOk_344 : osOk 344 [(79, 32), (175, 289), (271, 438), (367, 587), (463, 736), (537, 850)] = true := by decide +kernel

end
end LeanVM.Guest.End
