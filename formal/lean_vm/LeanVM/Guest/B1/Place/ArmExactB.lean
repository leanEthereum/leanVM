/-
  LeanVM.Guest.B1.Place.ArmExactB

  `armExactOk` of `open_stacked`'s arms 6 to 10, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact6 : armExactOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true := by
  decide +kernel

theorem armExact7 : armExactOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true := by
  decide +kernel

theorem armExact8 : armExactOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true := by
  decide +kernel

theorem armExact9 : armExactOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true := by
  decide +kernel

theorem armExact10 : armExactOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
