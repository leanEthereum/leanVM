module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_15 : wStaticRange 15 1 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_16_0 : noTopRet ((Data.core16.body.drop 0).take 222) = true ∧
    blockR (wlookJ 16) (womLookJ 16) true [] Data.core16.params Data.core16.name ((Data.core16.body.drop 0).take 222) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_16_222 : noTopRet ((Data.core16.body.drop 222).take 276) = true ∧
    blockR (wlookJ 16) (womLookJ 16) true [] Data.core16.params Data.core16.name ((Data.core16.body.drop 222).take 276) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_16_498 : blockR (wlookJ 16) (womLookJ 16) true [] Data.core16.params Data.core16.name (Data.core16.body.drop 498) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_0 : noTopRet ((Data.core17.body.drop 0).take 220) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 0).take 220) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_220 : noTopRet ((Data.core17.body.drop 220).take 1) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 220).take 1) ([], []) = some (⟨49, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_17_221 : noTopRet ((Data.core17.body.drop 221).take 11) = true ∧
    blockR (wlookJ 17) (womLookJ 17) true [] Data.core17.params Data.core17.name ((Data.core17.body.drop 221).take 11) ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
