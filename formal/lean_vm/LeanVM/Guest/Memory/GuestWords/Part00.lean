module

public import LeanVM.Guest.Memory.GuestWords.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem wstaticRange_0 : wStaticRange 0 11 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_11 : wStaticRange 11 7 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wstaticRange_18 : wStaticRange 18 1 := by
  unfold wStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 96) = true ∧
    blockR (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 96)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv true [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 96) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem wsplit_19_96 : blockR (wlookJ 19) (womLookJ 19) true [] Data.core19.params Data.core19.name (Data.core19.body.drop 96)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
