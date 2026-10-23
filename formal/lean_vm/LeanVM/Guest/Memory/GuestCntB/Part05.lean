module

public import LeanVM.Guest.Memory.GuestCntB.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwbsplit_17_392 : noTopRet ((Data.core17.body.drop 392).take 1) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 392).take 1) ([], []) = some (⟨7, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbsplit_17_393 : noTopRet ((Data.core17.body.drop 393).take 27) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 393).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbsplit_17_420 : noTopRet ((Data.core17.body.drop 420).take 1) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 420).take 1) ([], []) = some (⟨7, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwbsplit_17_421 : noTopRet ((Data.core17.body.drop 421).take 11) = true ∧
    blockR (kwblookJ 17) (kwbomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 421).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
