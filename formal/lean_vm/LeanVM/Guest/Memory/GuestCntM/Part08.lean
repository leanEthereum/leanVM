module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmsplit_17_512 : noTopRet ((Data.core17.body.drop 512).take 1) = true ∧
    blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 512).take 1) ([], []) = some (⟨1, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_17_513 : noTopRet ((Data.core17.body.drop 513).take 264) = true ∧
    blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 513).take 264) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_17_777 : blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name (Data.core17.body.drop 777) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_18 : kwmStaticRange 18 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_48 : kwmStaticRange 48 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_78 : kwmStaticRange 78 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_108 : kwmStaticRange 108 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_138 : kwmStaticRange 138 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_168 : kwmStaticRange 168 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
