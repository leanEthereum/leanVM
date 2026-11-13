/-
  LeanVM.Guest.B1.Place.ArmMuteA

  `armMuteOk` of `open_stacked`'s arms 0 to 5, by the kernel.
-/

module

public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1.Whir

@[expose] public section

theorem armMute0 : armMuteOk ("open_stacked__L" ++ natStr 0) idx% «open_stacked__L0» = true := by
  decide +kernel

theorem armMute1 : armMuteOk ("open_stacked__L" ++ natStr 1) idx% «open_stacked__L1» = true := by
  decide +kernel

theorem armMute2 : armMuteOk ("open_stacked__L" ++ natStr 2) idx% «open_stacked__L2» = true := by
  decide +kernel

theorem armMute3 : armMuteOk ("open_stacked__L" ++ natStr 3) idx% «open_stacked__L3» = true := by
  decide +kernel

theorem armMute4 : armMuteOk ("open_stacked__L" ++ natStr 4) idx% «open_stacked__L4» = true := by
  decide +kernel

theorem armMute5 : armMuteOk ("open_stacked__L" ++ natStr 5) idx% «open_stacked__L5» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
