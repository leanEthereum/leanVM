/-
  LeanVM.Guest.B1.Place.ArmExact5

  `armExactOk` of `open_stacked`'s arm 5, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact5 : armExactOk ("open_stacked__L" ++ natStr 5) idx% «open_stacked__L5» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
