module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wsplit_17_432 : noTopRet ((Data.core17.body.drop 432).take 1) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 432).take 1) ([], []) = some (⟨49, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_433 : noTopRet ((Data.core17.body.drop 433).take 27) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 433).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_460 : noTopRet ((Data.core17.body.drop 460).take 1) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 460).take 1) ([], []) = some (⟨49, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_461 : noTopRet ((Data.core17.body.drop 461).take 11) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 461).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
