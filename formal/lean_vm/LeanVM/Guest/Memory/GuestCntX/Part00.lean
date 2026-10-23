module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxstaticRange_0 : kwxStaticRange 0 16 := by
  unfold kwxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_16_0 : noTopRet ((Data.core16.body.drop 0).take 222) = true ∧
    blockR (kwxlookJ 16) (kwxomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 0).take 222) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_16_222 : noTopRet ((Data.core16.body.drop 222).take 276) = true ∧
    blockR (kwxlookJ 16) (kwxomLookJ 16) false [] Data.core16.params Data.core16.name ((Data.core16.body.drop 222).take 276) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_16_498 : blockR (kwxlookJ 16) (kwxomLookJ 16) false [] Data.core16.params Data.core16.name (Data.core16.body.drop 498) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_0 : noTopRet ((Data.core17.body.drop 0).take 220) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 0).take 220) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_220 : noTopRet ((Data.core17.body.drop 220).take 1) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 220).take 1) ([], []) = some (⟨6, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_221 : noTopRet ((Data.core17.body.drop 221).take 11) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 221).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
