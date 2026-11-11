module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_0 : kwmStaticRange 0 11 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_11 : kwmStaticRange 11 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_18 : kwmStaticRange 18 1 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmsplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 96) = true ∧
    blockR (kwmlookJ 19) (kwmomLookJ 19) false [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 96)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 96) = ([], []) := by
  decide +kernel

end
end LeanVM.Guest
