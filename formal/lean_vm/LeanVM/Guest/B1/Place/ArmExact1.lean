/-
  LeanVM.Guest.B1.Place.ArmExact1

  `armExactOk` of `open_stacked`'s arm 1, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armExact1 : armExactOk ("open_stacked__L" ++ natStr 1) idx% «open_stacked__L1» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
