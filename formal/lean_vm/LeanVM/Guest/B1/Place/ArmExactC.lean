/-
  LeanVM.Guest.B1.Place.ArmExactC

  `armExactOk` of `open_stacked`'s arms 9 to 10, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact9 : armExactOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true := by
  decide +kernel

theorem armExact10 : armExactOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
