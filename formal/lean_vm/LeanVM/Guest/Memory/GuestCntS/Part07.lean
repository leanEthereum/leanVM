module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwssplit_17_472 : noTopRet ((Data.core17.body.drop 472).take 1) = true ∧
    blockR (kwslookJ 17) (kwsomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 472).take 1) ([], []) = some (⟨14, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwssplit_17_473 : noTopRet ((Data.core17.body.drop 473).take 27) = true ∧
    blockR (kwslookJ 17) (kwsomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 473).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwssplit_17_500 : noTopRet ((Data.core17.body.drop 500).take 1) = true ∧
    blockR (kwslookJ 17) (kwsomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 500).take 1) ([], []) = some (⟨14, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwssplit_17_501 : noTopRet ((Data.core17.body.drop 501).take 11) = true ∧
    blockR (kwslookJ 17) (kwsomLookJ 17) false [] Data.core17.params Data.core17.name ((Data.core17.body.drop 501).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
