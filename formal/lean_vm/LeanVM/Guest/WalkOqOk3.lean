/-
  LeanVM.Guest.WalkOqOk3

  The certificates of a quarter of `opening_queries`' specializations and loops (those whose
  templates `B1/Opening/QueriesBody3.lean` checks) hand on the walk's obligations in the forms
  `WalkKnownDefs` checks, by kernel evaluation.
-/

module

public import LeanVM.Guest.WalkKnownDefs

namespace LeanVM.Guest.End

open LeanVM.Guest.B1

@[expose] public section

/-- `opening_queries__L0_L1_L64_L32_L17_L5`. -/
theorem walkOk_1116 : mainOkS 1116 0 ⟨1, 64, 12, 5⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L16_L4`. -/
theorem walkOk_1126 : mainOkS 1126 0 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L17_L5`. -/
theorem walkOk_1158 : mainOkS 1158 1 ⟨1, 64, 12, 5⟩ = true := by decide +kernel

/-- `opening_queries__L0_L1_L64_L32_L19_L7`. -/
theorem walkOk_1200 : mainOkS 1200 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L19_L7`. -/
theorem walkOk_1241 : mainOkS 1241 0 ⟨0, 16, 12, 7⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L21_L3`. -/
theorem walkOk_1307 : mainOkS 1307 1 ⟨1, 64, 18, 3⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L22_L4`. -/
theorem walkOk_1347 : mainOkS 1347 1 ⟨1, 64, 18, 4⟩ = true := by decide +kernel

/-- `opening_queries__L0_L1_L64_L32_L24_L6`. -/
theorem walkOk_1386 : mainOkS 1386 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L24_L6`. -/
theorem walkOk_1428 : mainOkS 1428 0 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L26_L2`. -/
theorem walkOk_1502 : mainOkS 1502 1 ⟨1, 64, 24, 2⟩ = true := by decide +kernel

/-- `opening_queries__L0_L0_L16_L24_L27_L3`. -/
theorem walkOk_1550 : mainOkS 1550 0 ⟨0, 16, 24, 3⟩ = true := by decide +kernel

/-- `opening_queries__L1_L1_L64_L32_L30_L6`. -/
theorem walkOk_1640 : mainOkS 1640 1 ⟨1, 64, 24, 6⟩ = true := by decide +kernel

/-- `__loop623`. -/
theorem walkOk_1695 : loop1Ok 1695 0 ⟨1, 64, 12, 5⟩ = true := by decide +kernel

/-- `__loop627`. -/
theorem walkOk_1701 : loop0Ok 1701 ⟨0, 16, 12, 4⟩ = true := by decide +kernel

/-- `__loop631`. -/
theorem walkOk_1712 : loop1Ok 1712 1 ⟨1, 64, 12, 5⟩ = true := by decide +kernel

/-- `__loop635`. -/
theorem walkOk_1722 : loop1Ok 1722 0 ⟨1, 64, 12, 7⟩ = true := by decide +kernel

/-- `__loop639`. -/
theorem walkOk_1732 : loop0Ok 1732 ⟨0, 16, 12, 7⟩ = true := by decide +kernel

/-- `__loop643`. -/
theorem walkOk_1745 : loop1Ok 1745 1 ⟨1, 64, 18, 3⟩ = true := by decide +kernel

/-- `__loop647`. -/
theorem walkOk_1753 : loop1Ok 1753 1 ⟨1, 64, 18, 4⟩ = true := by decide +kernel

/-- `__loop651`. -/
theorem walkOk_1760 : loop1Ok 1760 0 ⟨1, 64, 18, 6⟩ = true := by decide +kernel

/-- `__loop655`. -/
theorem walkOk_1767 : loop0Ok 1767 ⟨0, 16, 18, 6⟩ = true := by decide +kernel

/-- `__loop659`. -/
theorem walkOk_1777 : loop1Ok 1777 1 ⟨1, 64, 24, 2⟩ = true := by decide +kernel

/-- `__loop663`. -/
theorem walkOk_1785 : loop0Ok 1785 ⟨0, 16, 24, 3⟩ = true := by decide +kernel

/-- `__loop667`. -/
theorem walkOk_1796 : loop1Ok 1796 1 ⟨1, 64, 24, 6⟩ = true := by decide +kernel

end
end LeanVM.Guest.End
