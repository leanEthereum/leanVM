/-
  LeanVM.Guest.B1.Whir.CHonNamesAll

  Every candidate's callees' kinds.
-/

module

public import LeanVM.Guest.B1.Whir.CHonNames0
public import LeanVM.Guest.B1.Whir.CHonNames1
public import LeanVM.Guest.B1.Whir.CHonNames2
public import LeanVM.Guest.B1.Whir.CHonNames3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every candidate's callees' kinds.** -/
theorem honNames_all (m : ℕ) (h : m < 28) : HonNames (osCfg m) := by
  interval_cases m
  · exact honNames_0
  · exact honNames_1
  · exact honNames_2
  · exact honNames_3
  · exact honNames_4
  · exact honNames_5
  · exact honNames_6
  · exact honNames_7
  · exact honNames_8
  · exact honNames_9
  · exact honNames_10
  · exact honNames_11
  · exact honNames_12
  · exact honNames_13
  · exact honNames_14
  · exact honNames_15
  · exact honNames_16
  · exact honNames_17
  · exact honNames_18
  · exact honNames_19
  · exact honNames_20
  · exact honNames_21
  · exact honNames_22
  · exact honNames_23
  · exact honNames_24
  · exact honNames_25
  · exact honNames_26
  · exact honNames_27

end
end LeanVM.Guest.B1.Whir
