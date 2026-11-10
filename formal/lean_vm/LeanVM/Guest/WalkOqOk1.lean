/-
  LeanVM.Guest.WalkOqOk1

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody1.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

/-- `opening_queries__L0_L1_L64_L32_L15_L3`. -/
theorem walkOk_1112 : mainOkS 1112 0 ⟨1, 64, 12, 3⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L14_L2`. -/
theorem walkOk_1124 : mainOkS 1124 0 ⟨0, 16, 12, 2⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L15_L3`. -/
theorem walkOk_1156 : mainOkS 1156 1 ⟨1, 64, 12, 3⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L17_L5`. -/
theorem walkOk_1163 : mainOkS 1163 0 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L19_L7`. -/
theorem walkOk_1236 : mainOkS 1236 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

/-- `opening_queries__L0_L1_L64_L32_L21_L3`. -/
theorem walkOk_1275 : mainOkS 1275 0 ⟨1, 64, 18, 3⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L21_L3`. -/
theorem walkOk_1312 : mainOkS 1312 0 ⟨0, 16, 18, 3⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L22_L4`. -/
theorem walkOk_1351 : mainOkS 1351 0 ⟨0, 16, 18, 4⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L24_L6`. -/
theorem walkOk_1423 : mainOkS 1423 1 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

/-- `opening_queries__L0_L1_L64_L32_L26_L2`. -/
theorem walkOk_1461 : mainOkS 1461 0 ⟨1, 64, 24, 2⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L26_L2`. -/
theorem walkOk_1507 : mainOkS 1507 0 ⟨0, 16, 24, 2⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L29_L5`. -/
theorem walkOk_1594 : mainOkS 1594 1 ⟨1, 64, 24, 5⟩ = true := by decide +kernel

/-- `__loop621`. -/
theorem walkOk_1692 : loop1Ok 1692 0 ⟨1, 64, 12, 3⟩ = true := by decide +kernel

/-- `__loop625`. -/
theorem walkOk_1699 : loop0Ok 1699 ⟨0, 16, 12, 2⟩ = true := by decide +kernel

/-- `__loop629`. -/
theorem walkOk_1709 : loop1Ok 1709 1 ⟨1, 64, 12, 3⟩ = true := by decide +kernel

/-- `__loop633`. -/
theorem walkOk_1714 : loop0Ok 1714 ⟨0, 16, 12, 5⟩ = true := by decide +kernel

/-- `__loop637`. -/
theorem walkOk_1730 : loop1Ok 1730 1 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

/-- `__loop641`. -/
theorem walkOk_1740 : loop1Ok 1740 0 ⟨1, 64, 18, 3⟩ = true := by decide +kernel

/-- `__loop645`. -/
theorem walkOk_1747 : loop0Ok 1747 ⟨0, 16, 18, 3⟩ = true := by decide +kernel

/-- `__loop649`. -/
theorem walkOk_1755 : loop0Ok 1755 ⟨0, 16, 18, 4⟩ = true := by decide +kernel

/-- `__loop653`. -/
theorem walkOk_1765 : loop1Ok 1765 1 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

/-- `__loop657`. -/
theorem walkOk_1772 : loop1Ok 1772 0 ⟨1, 64, 24, 2⟩ = true := by decide +kernel

/-- `__loop661`. -/
theorem walkOk_1780 : loop0Ok 1780 ⟨0, 16, 24, 2⟩ = true := by decide +kernel

/-- `__loop665`. -/
theorem walkOk_1791 : loop1Ok 1791 1 ⟨1, 64, 24, 5⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
