/-
  LeanVM.Guest.B1.Place.ArmExactC

  `armExactOk` of `open_stacked`'s arms 9 and 10, by the kernel: each arm's callees forty at a time.
-/

module

public import LeanVM.Guest.B1.Place.ArmExactDef

namespace LeanVM.Guest.B1.Arm

open LeanVM.Guest.Core LeanVM.Guest.B1.Whir

@[expose] public section

private theorem chunk9_0 : armChunk idx% «open_stacked__L9» 0 = true := by decide +kernel
private theorem chunk9_1 : armChunk idx% «open_stacked__L9» 1 = true := by decide +kernel
private theorem chunk9_2 : armChunk idx% «open_stacked__L9» 2 = true := by decide +kernel
private theorem chunk9_3 : armChunk idx% «open_stacked__L9» 3 true = true := by decide +kernel

theorem armExact9 : armExactOk ("open_stacked__L" ++ natStr 9) idx% «open_stacked__L9» = true :=
  armExactOk_of_chunks (fn := fn% «open_stacked__L9») rfl (by decide +kernel) (by decide +kernel)
    chunk9_0 chunk9_1 chunk9_2 chunk9_3

private theorem chunk10_0 : armChunk idx% «open_stacked__L10» 0 = true := by decide +kernel
private theorem chunk10_1 : armChunk idx% «open_stacked__L10» 1 = true := by decide +kernel
private theorem chunk10_2 : armChunk idx% «open_stacked__L10» 2 = true := by decide +kernel
private theorem chunk10_3 : armChunk idx% «open_stacked__L10» 3 true = true := by decide +kernel

theorem armExact10 : armExactOk ("open_stacked__L" ++ natStr 10) idx% «open_stacked__L10» = true :=
  armExactOk_of_chunks (fn := fn% «open_stacked__L10») rfl (by decide +kernel) (by decide +kernel)
    chunk10_0 chunk10_1 chunk10_2 chunk10_3

end
end LeanVM.Guest.B1.Arm
