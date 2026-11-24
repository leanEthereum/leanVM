/-
  LeanVM.Guest.B1.Place.ArmOkB

  `armExactOk` and `armMuteOk` of `open_stacked`'s arms 6 to 10, by the kernel, an arm's two in one evaluation
  of its body and callees.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef
public import LeanVM.Guest.B1.Place.ArmMuteDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

theorem armOk6 :
    armExactOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true := by
  decide +kernel

theorem armOk7 :
    armExactOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true := by
  decide +kernel

theorem armOk8 :
    armExactOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true := by
  decide +kernel

theorem armOk9 :
    armExactOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true := by
  decide +kernel

theorem armOk10 :
    armExactOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true ∧
      armMuteOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true := by
  decide +kernel

end
end LeanVM.Guest.B1.Arm
