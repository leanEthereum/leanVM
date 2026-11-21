/-
  LeanVM.Guest.B1.Place.ArmMuteB

  `armMuteOk` of `open_stacked`'s arms 6 to 10, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armMute6 : armMuteOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true := by
  decide +kernel

theorem armMute7 : armMuteOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true := by
  decide +kernel

theorem armMute8 : armMuteOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true := by
  decide +kernel

theorem armMute9 : armMuteOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true := by
  decide +kernel

theorem armMute10 : armMuteOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
