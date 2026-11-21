/-
  LeanVM.Guest.B1.Place.ArmExact2

  `armExactOk` of `open_stacked`'s arm 2, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact2 : armExactOk ("open_stacked__L" ++ natStr 2) idx% «open_stacked__L2» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
