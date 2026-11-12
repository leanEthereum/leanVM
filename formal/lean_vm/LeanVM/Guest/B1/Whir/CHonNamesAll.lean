/-
  LeanVM.Guest.B1.Whir.CHonNamesAll

  Every arm's callees' kinds at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames0
public import LeanVM.Guest.B1.Whir.CHonNames1
public import LeanVM.Guest.B1.Whir.CHonNames2
public import LeanVM.Guest.B1.Whir.CHonNames3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every arm at every rate.** -/
theorem honNames_all (m ri : ℕ) (hm : m < 11) (hr : ri < 4) : HonNames (osCfgR m ri) := by
  interval_cases m <;> interval_cases ri
  · exact honNames_0_0
  · exact honNames_0_1
  · exact honNames_0_2
  · exact honNames_0_3
  · exact honNames_1_0
  · exact honNames_1_1
  · exact honNames_1_2
  · exact honNames_1_3
  · exact honNames_2_0
  · exact honNames_2_1
  · exact honNames_2_2
  · exact honNames_2_3
  · exact honNames_3_0
  · exact honNames_3_1
  · exact honNames_3_2
  · exact honNames_3_3
  · exact honNames_4_0
  · exact honNames_4_1
  · exact honNames_4_2
  · exact honNames_4_3
  · exact honNames_5_0
  · exact honNames_5_1
  · exact honNames_5_2
  · exact honNames_5_3
  · exact honNames_6_0
  · exact honNames_6_1
  · exact honNames_6_2
  · exact honNames_6_3
  · exact honNames_7_0
  · exact honNames_7_1
  · exact honNames_7_2
  · exact honNames_7_3
  · exact honNames_8_0
  · exact honNames_8_1
  · exact honNames_8_2
  · exact honNames_8_3
  · exact honNames_9_0
  · exact honNames_9_1
  · exact honNames_9_2
  · exact honNames_9_3
  · exact honNames_10_0
  · exact honNames_10_1
  · exact honNames_10_2
  · exact honNames_10_3

end
end LeanVM.Guest.B1.Whir
