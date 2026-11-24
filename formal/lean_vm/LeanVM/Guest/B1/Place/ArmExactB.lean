/-
  LeanVM.Guest.B1.Place.ArmExactB

  `armExactOk` of `open_stacked`'s arms 6 to 8, by the kernel: each arm's callees forty at a time.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

private theorem chunk6_0 : armChunk idx% «open_stacked__L6» 0 = true := by decide +kernel
private theorem chunk6_1 : armChunk idx% «open_stacked__L6» 1 = true := by decide +kernel
private theorem chunk6_2 : armChunk idx% «open_stacked__L6» 2 = true := by decide +kernel
private theorem chunk6_3 : armChunk idx% «open_stacked__L6» 3 true = true := by decide +kernel

theorem armExact6 : armExactOk ("open_stacked__L" ++ natStr 6) idx% «open_stacked__L6» = true :=
  armExactOk_of_chunks (fn := fn% «open_stacked__L6») rfl (by decide +kernel) (by decide +kernel)
    chunk6_0 chunk6_1 chunk6_2 chunk6_3

private theorem chunk7_0 : armChunk idx% «open_stacked__L7» 0 = true := by decide +kernel
private theorem chunk7_1 : armChunk idx% «open_stacked__L7» 1 = true := by decide +kernel
private theorem chunk7_2 : armChunk idx% «open_stacked__L7» 2 = true := by decide +kernel
private theorem chunk7_3 : armChunk idx% «open_stacked__L7» 3 true = true := by decide +kernel

theorem armExact7 : armExactOk ("open_stacked__L" ++ natStr 7) idx% «open_stacked__L7» = true :=
  armExactOk_of_chunks (fn := fn% «open_stacked__L7») rfl (by decide +kernel) (by decide +kernel)
    chunk7_0 chunk7_1 chunk7_2 chunk7_3

private theorem chunk8_0 : armChunk idx% «open_stacked__L8» 0 = true := by decide +kernel
private theorem chunk8_1 : armChunk idx% «open_stacked__L8» 1 = true := by decide +kernel
private theorem chunk8_2 : armChunk idx% «open_stacked__L8» 2 = true := by decide +kernel
private theorem chunk8_3 : armChunk idx% «open_stacked__L8» 3 true = true := by decide +kernel

theorem armExact8 : armExactOk ("open_stacked__L" ++ natStr 8) idx% «open_stacked__L8» = true :=
  armExactOk_of_chunks (fn := fn% «open_stacked__L8») rfl (by decide +kernel) (by decide +kernel)
    chunk8_0 chunk8_1 chunk8_2 chunk8_3

end
end LeanVM.Guest.B1.Arm
