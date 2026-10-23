module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxsplit_17_352 : noTopRet ((Data.core17.body.drop 352).take 1) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 352).take 1) ([], []) = some (⟨6, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_353 : noTopRet ((Data.core17.body.drop 353).take 27) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 353).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_380 : noTopRet ((Data.core17.body.drop 380).take 1) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 380).take 1) ([], []) = some (⟨6, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxsplit_17_381 : noTopRet ((Data.core17.body.drop 381).take 11) = true ∧
    blockR (kwxlookJ 17) (kwxomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 381).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
