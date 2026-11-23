/-
  LeanVM.Guest.B1.Place.ArmMute10

  `armMuteOk` of `open_stacked`'s arm 10, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armMute10 : armMuteOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
