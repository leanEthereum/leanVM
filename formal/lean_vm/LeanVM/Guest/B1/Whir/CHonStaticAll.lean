/-
  LeanVM.Guest.B1.Whir.CHonStaticAll

  Every candidate's honest buffers' configuration facts.
-/

module

public import LeanVM.Guest.B1.Whir.CHonStatic0
public import LeanVM.Guest.B1.Whir.CHonStatic1
public import LeanVM.Guest.B1.Whir.CHonStatic2
public import LeanVM.Guest.B1.Whir.CHonStatic3

namespace LeanVM.Guest.B1.Whir

@[expose] public section

/-- **Every candidate's honest buffers' configuration facts.** -/
theorem honStatic_all (m : ℕ) (h : m < 28) : HonStatic (osCfg m) := by
  interval_cases m
  · exact honStatic_0
  · exact honStatic_1
  · exact honStatic_2
  · exact honStatic_3
  · exact honStatic_4
  · exact honStatic_5
  · exact honStatic_6
  · exact honStatic_7
  · exact honStatic_8
  · exact honStatic_9
  · exact honStatic_10
  · exact honStatic_11
  · exact honStatic_12
  · exact honStatic_13
  · exact honStatic_14
  · exact honStatic_15
  · exact honStatic_16
  · exact honStatic_17
  · exact honStatic_18
  · exact honStatic_19
  · exact honStatic_20
  · exact honStatic_21
  · exact honStatic_22
  · exact honStatic_23
  · exact honStatic_24
  · exact honStatic_25
  · exact honStatic_26
  · exact honStatic_27

end
end LeanVM.Guest.B1.Whir
