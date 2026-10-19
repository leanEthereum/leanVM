module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wsplit_17_272 : noTopRet ((Data.core17.body.drop 272).take 1) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 272).take 1) ([], []) = some (⟨49, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_273 : noTopRet ((Data.core17.body.drop 273).take 27) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 273).take 27) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_300 : noTopRet ((Data.core17.body.drop 300).take 1) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 300).take 1) ([], []) = some (⟨49, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_301 : noTopRet ((Data.core17.body.drop 301).take 11) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 301).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
