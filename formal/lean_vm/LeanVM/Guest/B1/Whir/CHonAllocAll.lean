/-
  LeanVM.Guest.B1.Whir.CHonAllocAll

  Every arm's body allocations at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc0
public import LeanVM.Guest.B1.Whir.CHonAlloc1
public import LeanVM.Guest.B1.Whir.CHonAlloc2
public import LeanVM.Guest.B1.Whir.CHonAlloc3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every arm at every rate.** -/
theorem bodyStatic_all (m ri : ℕ) (hm : m < 11) (hr : ri < 4) : BodyStatic (osCfgR m ri) := by
  interval_cases m <;> interval_cases ri
  · exact bodyStatic_0_0
  · exact bodyStatic_0_1
  · exact bodyStatic_0_2
  · exact bodyStatic_0_3
  · exact bodyStatic_1_0
  · exact bodyStatic_1_1
  · exact bodyStatic_1_2
  · exact bodyStatic_1_3
  · exact bodyStatic_2_0
  · exact bodyStatic_2_1
  · exact bodyStatic_2_2
  · exact bodyStatic_2_3
  · exact bodyStatic_3_0
  · exact bodyStatic_3_1
  · exact bodyStatic_3_2
  · exact bodyStatic_3_3
  · exact bodyStatic_4_0
  · exact bodyStatic_4_1
  · exact bodyStatic_4_2
  · exact bodyStatic_4_3
  · exact bodyStatic_5_0
  · exact bodyStatic_5_1
  · exact bodyStatic_5_2
  · exact bodyStatic_5_3
  · exact bodyStatic_6_0
  · exact bodyStatic_6_1
  · exact bodyStatic_6_2
  · exact bodyStatic_6_3
  · exact bodyStatic_7_0
  · exact bodyStatic_7_1
  · exact bodyStatic_7_2
  · exact bodyStatic_7_3
  · exact bodyStatic_8_0
  · exact bodyStatic_8_1
  · exact bodyStatic_8_2
  · exact bodyStatic_8_3
  · exact bodyStatic_9_0
  · exact bodyStatic_9_1
  · exact bodyStatic_9_2
  · exact bodyStatic_9_3
  · exact bodyStatic_10_0
  · exact bodyStatic_10_1
  · exact bodyStatic_10_2
  · exact bodyStatic_10_3

end
end LeanVM.Guest.B1.Whir
