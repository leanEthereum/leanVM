/-
  LeanVM.Guest.B1.Whir.CHonAllocAll

  Every candidate's body allocations.
-/

module

public import LeanVM.Guest.B1.Whir.CHonAlloc0
public import LeanVM.Guest.B1.Whir.CHonAlloc1
public import LeanVM.Guest.B1.Whir.CHonAlloc2
public import LeanVM.Guest.B1.Whir.CHonAlloc3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

theorem bodyStatic_all (m : ℕ) (h : m < 28) : BodyStatic (osCfg m) := by
  interval_cases m
  · exact bodyStatic_0
  · exact bodyStatic_1
  · exact bodyStatic_2
  · exact bodyStatic_3
  · exact bodyStatic_4
  · exact bodyStatic_5
  · exact bodyStatic_6
  · exact bodyStatic_7
  · exact bodyStatic_8
  · exact bodyStatic_9
  · exact bodyStatic_10
  · exact bodyStatic_11
  · exact bodyStatic_12
  · exact bodyStatic_13
  · exact bodyStatic_14
  · exact bodyStatic_15
  · exact bodyStatic_16
  · exact bodyStatic_17
  · exact bodyStatic_18
  · exact bodyStatic_19
  · exact bodyStatic_20
  · exact bodyStatic_21
  · exact bodyStatic_22
  · exact bodyStatic_23
  · exact bodyStatic_24
  · exact bodyStatic_25
  · exact bodyStatic_26
  · exact bodyStatic_27

end
end LeanVM.Guest.B1.Whir
