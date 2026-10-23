module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjsplit_17_432 : noTopRet ((Data.core17.body.drop 432).take 1) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 432).take 1) ([], []) = some (⟨1, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_17_433 : noTopRet ((Data.core17.body.drop 433).take 27) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 433).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_17_460 : noTopRet ((Data.core17.body.drop 460).take 1) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 460).take 1) ([], []) = some (⟨1, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwjsplit_17_461 : noTopRet ((Data.core17.body.drop 461).take 11) = true ∧
    blockR (kwjlookJ 17) (kwjomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 461).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
