module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_0 : kwmStaticRange 0 16 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_16_0 : noTopRet ((Data.core16.body.drop 0).take 222) = true ∧
    blockR (kwmlookJ 16) (kwmomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 0).take 222) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_16_222 : noTopRet ((Data.core16.body.drop 222).take 276) = true ∧
    blockR (kwmlookJ 16) (kwmomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 222).take 276) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_16_498 : blockR (kwmlookJ 16) (kwmomLookJ 16) false [] Data.core16.params Data.core16.name (Data.core16.body.drop 498) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_17_0 : noTopRet ((Data.core17.body.drop 0).take 220) = true ∧
    blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 0).take 220) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_17_220 : noTopRet ((Data.core17.body.drop 220).take 1) = true ∧
    blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 220).take 1) ([], []) = some (⟨1, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_17_221 : noTopRet ((Data.core17.body.drop 221).take 11) = true ∧
    blockR (kwmlookJ 17) (kwmomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 221).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
