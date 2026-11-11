/-
  LeanVM.Guest.WalkWpOk

  The certificates of `walk_path`'s specializations take its windows (`winsTag`) and hand on only
  their bounds (`wpOk`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

@[expose] public section

/-- `walk_path__L12_L3`. -/
theorem walkOk_1439 : wpOkJ 1439 12 3 = true := by decide +kernel

/-- `walk_path__L12_L5`. -/
theorem walkOk_1442 : wpOkJ 1442 12 5 = true := by decide +kernel

/-- `walk_path__L12_L4`. -/
theorem walkOk_1459 : wpOkJ 1459 12 4 = true := by decide +kernel

/-- `walk_path__L12_L6`. -/
theorem walkOk_1462 : wpOkJ 1462 12 6 = true := by decide +kernel

/-- `walk_path__L12_L7`. -/
theorem walkOk_1471 : wpOkJ 1471 12 7 = true := by decide +kernel

/-- `walk_path__L18_L2`. -/
theorem walkOk_1480 : wpOkJ 1480 18 2 = true := by decide +kernel

/-- `walk_path__L18_L3`. -/
theorem walkOk_1489 : wpOkJ 1489 18 3 = true := by decide +kernel

/-- `walk_path__L18_L4`. -/
theorem walkOk_1497 : wpOkJ 1497 18 4 = true := by decide +kernel

/-- `walk_path__L18_L5`. -/
theorem walkOk_1503 : wpOkJ 1503 18 5 = true := by decide +kernel

/-- `walk_path__L18_L6`. -/
theorem walkOk_1509 : wpOkJ 1509 18 6 = true := by decide +kernel

/-- `walk_path__L18_L7`. -/
theorem walkOk_1515 : wpOkJ 1515 18 7 = true := by decide +kernel

/-- `walk_path__L24_L2`. -/
theorem walkOk_1521 : wpOkJ 1521 24 2 = true := by decide +kernel

/-- `walk_path__L24_L3`. -/
theorem walkOk_1523 : wpOkJ 1523 24 3 = true := by decide +kernel

/-- `walk_path__L24_L4`. -/
theorem walkOk_1528 : wpOkJ 1528 24 4 = true := by decide +kernel

/-- `walk_path__L12_L2`. -/
theorem walkOk_1532 : wpOkJ 1532 12 2 = true := by decide +kernel

/-- `walk_path__L6_L7`. -/
theorem walkOk_1533 : wpOkJ 1533 6 7 = true := by decide +kernel

/-- `walk_path__L6_L6`. -/
theorem walkOk_1534 : wpOkJ 1534 6 6 = true := by decide +kernel

/-- `walk_path__L12_L8`. -/
theorem walkOk_1535 : wpOkJ 1535 12 8 = true := by decide +kernel

end
end LeanVM.Guest.End
