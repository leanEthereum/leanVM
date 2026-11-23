/-
  LeanVM.Guest.B1.Place.ArmExact3

  `armExactOk` of `open_stacked`'s arm 3, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact3 : armExactOk ("open_stacked__L" ++ natStr 3) idx% «open_stacked__L3» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
