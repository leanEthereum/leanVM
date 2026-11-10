/-
  LeanVM.Guest.WalkWpOk

  The certificates of `walk_path`'s specializations take its windows (`winsTag`) and hand on only
  their bounds (`wpOk`), by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

@[expose] public section

/-- `walk_path__L6_L8`. -/
theorem walkOk_1690 : wpOkJ 1690 6 8 = true := by decide +kernel

/-- `walk_path__L12_L4`. -/
theorem walkOk_1693 : wpOkJ 1693 12 4 = true := by decide +kernel

/-- `walk_path__L12_L3`. -/
theorem walkOk_1708 : wpOkJ 1708 12 3 = true := by decide +kernel

/-- `walk_path__L12_L5`. -/
theorem walkOk_1711 : wpOkJ 1711 12 5 = true := by decide +kernel

/-- `walk_path__L12_L6`. -/
theorem walkOk_1720 : wpOkJ 1720 12 6 = true := by decide +kernel

/-- `walk_path__L12_L7`. -/
theorem walkOk_1729 : wpOkJ 1729 12 7 = true := by decide +kernel

/-- `walk_path__L18_L2`. -/
theorem walkOk_1738 : wpOkJ 1738 18 2 = true := by decide +kernel

/-- `walk_path__L18_L3`. -/
theorem walkOk_1744 : wpOkJ 1744 18 3 = true := by decide +kernel

/-- `walk_path__L18_L4`. -/
theorem walkOk_1752 : wpOkJ 1752 18 4 = true := by decide +kernel

/-- `walk_path__L18_L5`. -/
theorem walkOk_1758 : wpOkJ 1758 18 5 = true := by decide +kernel

/-- `walk_path__L18_L6`. -/
theorem walkOk_1764 : wpOkJ 1764 18 6 = true := by decide +kernel

/-- `walk_path__L18_L7`. -/
theorem walkOk_1770 : wpOkJ 1770 18 7 = true := by decide +kernel

/-- `walk_path__L24_L2`. -/
theorem walkOk_1776 : wpOkJ 1776 24 2 = true := by decide +kernel

/-- `walk_path__L24_L3`. -/
theorem walkOk_1778 : wpOkJ 1778 24 3 = true := by decide +kernel

/-- `walk_path__L24_L4`. -/
theorem walkOk_1783 : wpOkJ 1783 24 4 = true := by decide +kernel

/-- `walk_path__L24_L5`. -/
theorem walkOk_1790 : wpOkJ 1790 24 5 = true := by decide +kernel

/-- `walk_path__L24_L6`. -/
theorem walkOk_1795 : wpOkJ 1795 24 6 = true := by decide +kernel

/-- `walk_path__L6_L7`. -/
theorem walkOk_1799 : wpOkJ 1799 6 7 = true := by decide +kernel

/-- `walk_path__L12_L2`. -/
theorem walkOk_1800 : wpOkJ 1800 12 2 = true := by decide +kernel

/-- `walk_path__L6_L6`. -/
theorem walkOk_1801 : wpOkJ 1801 6 6 = true := by decide +kernel

/-- `walk_path__L12_L8`. -/
theorem walkOk_1802 : wpOkJ 1802 12 8 = true := by decide +kernel

/-- `walk_path__L18_L8`. -/
theorem walkOk_1803 : wpOkJ 1803 18 8 = true := by decide +kernel

end
end LeanVM.Guest.End
