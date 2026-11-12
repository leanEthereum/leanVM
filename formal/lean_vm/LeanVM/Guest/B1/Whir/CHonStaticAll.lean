/-
  LeanVM.Guest.B1.Whir.CHonStaticAll

  Every arm's buffer facts at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic0
public import LeanVM.Guest.B1.Whir.CHonStatic1
public import LeanVM.Guest.B1.Whir.CHonStatic2
public import LeanVM.Guest.B1.Whir.CHonStatic3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every arm at every rate.** -/
theorem honStatic_all (m ri : ℕ) (hm : m < 11) (hr : ri < 4) : HonStatic (osCfgR m ri) := by
  interval_cases m <;> interval_cases ri
  · exact honStatic_0_0
  · exact honStatic_0_1
  · exact honStatic_0_2
  · exact honStatic_0_3
  · exact honStatic_1_0
  · exact honStatic_1_1
  · exact honStatic_1_2
  · exact honStatic_1_3
  · exact honStatic_2_0
  · exact honStatic_2_1
  · exact honStatic_2_2
  · exact honStatic_2_3
  · exact honStatic_3_0
  · exact honStatic_3_1
  · exact honStatic_3_2
  · exact honStatic_3_3
  · exact honStatic_4_0
  · exact honStatic_4_1
  · exact honStatic_4_2
  · exact honStatic_4_3
  · exact honStatic_5_0
  · exact honStatic_5_1
  · exact honStatic_5_2
  · exact honStatic_5_3
  · exact honStatic_6_0
  · exact honStatic_6_1
  · exact honStatic_6_2
  · exact honStatic_6_3
  · exact honStatic_7_0
  · exact honStatic_7_1
  · exact honStatic_7_2
  · exact honStatic_7_3
  · exact honStatic_8_0
  · exact honStatic_8_1
  · exact honStatic_8_2
  · exact honStatic_8_3
  · exact honStatic_9_0
  · exact honStatic_9_1
  · exact honStatic_9_2
  · exact honStatic_9_3
  · exact honStatic_10_0
  · exact honStatic_10_1
  · exact honStatic_10_2
  · exact honStatic_10_3

end
end LeanVM.Guest.B1.Whir
