/-
  LeanVM.Guest.B1.Whir.FactsAll

  Every size's facts at every rate.
-/

module

public import LeanVM.Guest.B1.Whir.Facts0
public import LeanVM.Guest.B1.Whir.Facts1
public import LeanVM.Guest.B1.Whir.Facts2
public import LeanVM.Guest.B1.Whir.Facts3
public import LeanVM.Guest.B1.Whir.Facts4
public import LeanVM.Guest.B1.Whir.Facts5
public import LeanVM.Guest.B1.Whir.Facts6
public import LeanVM.Guest.B1.Whir.Facts7
public import LeanVM.Guest.B1.Whir.Facts8
public import LeanVM.Guest.B1.Whir.Facts9
public import LeanVM.Guest.B1.Whir.Facts10

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every size's facts at every rate.** -/
theorem candB_all (m ri : ℕ) (hm : m < ligNSizes) (hr : ri < 4) : candB m ri = true := by
  interval_cases m <;> interval_cases ri
  · exact candB_0_0
  · exact candB_0_1
  · exact candB_0_2
  · exact candB_0_3
  · exact candB_1_0
  · exact candB_1_1
  · exact candB_1_2
  · exact candB_1_3
  · exact candB_2_0
  · exact candB_2_1
  · exact candB_2_2
  · exact candB_2_3
  · exact candB_3_0
  · exact candB_3_1
  · exact candB_3_2
  · exact candB_3_3
  · exact candB_4_0
  · exact candB_4_1
  · exact candB_4_2
  · exact candB_4_3
  · exact candB_5_0
  · exact candB_5_1
  · exact candB_5_2
  · exact candB_5_3
  · exact candB_6_0
  · exact candB_6_1
  · exact candB_6_2
  · exact candB_6_3
  · exact candB_7_0
  · exact candB_7_1
  · exact candB_7_2
  · exact candB_7_3
  · exact candB_8_0
  · exact candB_8_1
  · exact candB_8_2
  · exact candB_8_3
  · exact candB_9_0
  · exact candB_9_1
  · exact candB_9_2
  · exact candB_9_3
  · exact candB_10_0
  · exact candB_10_1
  · exact candB_10_2
  · exact candB_10_3

end
end LeanVM.Guest.B1.Whir
