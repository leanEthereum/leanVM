/-
  LeanVM.Guest.WalkOsOk3

  The certificates of `open_stacked__L9`, `open_stacked__L10` assume the window table and hand on, at each level's dispatch into
  `level_queries`, the windows that level's `level_positions` dispatch decodes (`osOk`), by kernel
  evaluation.
-/

module

public import LeanVM.Guest.WalkOsDefs

namespace LeanVM.Guest.End

@[expose] public section

set_option maxRecDepth 100000 in
/-- `open_stacked__L9`. -/
theorem osOk_345 : osOk 345 [(79, 32), (175, 289), (271, 438), (367, 587), (463, 736), (537, 850)] = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- `open_stacked__L10`. -/
theorem osOk_346 : osOk 346 [(79, 32), (175, 289), (271, 438), (367, 587), (463, 736), (537, 850)] = true := by decide +kernel

end
end LeanVM.Guest.End
