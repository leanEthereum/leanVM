/-
  LeanVM.Guest.B1.Place.ArmOkA

  `armExactOk` and `armMuteOk` of `open_stacked`'s arms 0 to 5, by the kernel, an arm's two in one evaluation
  of its body and callees.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

theorem armOk0 :
    armExactOk ("open_stacked__L" ++ natStr 0) idx% «open_stacked__L0» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 0) idx% «open_stacked__L0» = true := by
  decide +kernel

theorem armOk1 :
    armExactOk ("open_stacked__L" ++ natStr 1) idx% «open_stacked__L1» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 1) idx% «open_stacked__L1» = true := by
  decide +kernel

theorem armOk2 :
    armExactOk ("open_stacked__L" ++ natStr 2) idx% «open_stacked__L2» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 2) idx% «open_stacked__L2» = true := by
  decide +kernel

theorem armOk3 :
    armExactOk ("open_stacked__L" ++ natStr 3) idx% «open_stacked__L3» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 3) idx% «open_stacked__L3» = true := by
  decide +kernel

theorem armOk4 :
    armExactOk ("open_stacked__L" ++ natStr 4) idx% «open_stacked__L4» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 4) idx% «open_stacked__L4» = true := by
  decide +kernel

theorem armOk5 :
    armExactOk ("open_stacked__L" ++ natStr 5) idx% «open_stacked__L5» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 5) idx% «open_stacked__L5» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
