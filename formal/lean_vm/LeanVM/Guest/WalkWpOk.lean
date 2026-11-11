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
theorem walkOk_1643 : wpOkJ 1643 12 3 = true := by decide +kernel

/-- `walk_path__L12_L5`. -/
theorem walkOk_1646 : wpOkJ 1646 12 5 = true := by decide +kernel

/-- `walk_path__L12_L4`. -/
theorem walkOk_1663 : wpOkJ 1663 12 4 = true := by decide +kernel

/-- `walk_path__L12_L6`. -/
theorem walkOk_1666 : wpOkJ 1666 12 6 = true := by decide +kernel

/-- `walk_path__L12_L7`. -/
theorem walkOk_1675 : wpOkJ 1675 12 7 = true := by decide +kernel

/-- `walk_path__L18_L2`. -/
theorem walkOk_1684 : wpOkJ 1684 18 2 = true := by decide +kernel

/-- `walk_path__L18_L3`. -/
theorem walkOk_1693 : wpOkJ 1693 18 3 = true := by decide +kernel

/-- `walk_path__L18_L4`. -/
theorem walkOk_1701 : wpOkJ 1701 18 4 = true := by decide +kernel

/-- `walk_path__L18_L5`. -/
theorem walkOk_1707 : wpOkJ 1707 18 5 = true := by decide +kernel

/-- `walk_path__L18_L6`. -/
theorem walkOk_1713 : wpOkJ 1713 18 6 = true := by decide +kernel

/-- `walk_path__L18_L7`. -/
theorem walkOk_1719 : wpOkJ 1719 18 7 = true := by decide +kernel

/-- `walk_path__L24_L2`. -/
theorem walkOk_1725 : wpOkJ 1725 24 2 = true := by decide +kernel

/-- `walk_path__L24_L3`. -/
theorem walkOk_1727 : wpOkJ 1727 24 3 = true := by decide +kernel

/-- `walk_path__L24_L4`. -/
theorem walkOk_1732 : wpOkJ 1732 24 4 = true := by decide +kernel

/-- `walk_path__L24_L5`. -/
theorem walkOk_1739 : wpOkJ 1739 24 5 = true := by decide +kernel

/-- `walk_path__L24_L6`. -/
theorem walkOk_1744 : wpOkJ 1744 24 6 = true := by decide +kernel

/-- `walk_path__L12_L2`. -/
theorem walkOk_1748 : wpOkJ 1748 12 2 = true := by decide +kernel

/-- `walk_path__L6_L7`. -/
theorem walkOk_1749 : wpOkJ 1749 6 7 = true := by decide +kernel

/-- `walk_path__L6_L6`. -/
theorem walkOk_1750 : wpOkJ 1750 6 6 = true := by decide +kernel

/-- `walk_path__L12_L8`. -/
theorem walkOk_1751 : wpOkJ 1751 12 8 = true := by decide +kernel

/-- `walk_path__L18_L8`. -/
theorem walkOk_1752 : wpOkJ 1752 18 8 = true := by decide +kernel

end
end LeanVM.Guest.End
