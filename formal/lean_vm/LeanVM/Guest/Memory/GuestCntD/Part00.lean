module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwdstaticRange_0 : kwdStaticRange 0 11 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_11 : kwdStaticRange 11 7 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdstaticRange_18 : kwdStaticRange 18 1 := by
  unfold kwdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_19_0 : noTopRet ((Data.core19.body.drop 0).take 96) = true ∧
    blockR (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name ((Data.core19.body.drop 0).take 96)
      ([], []) = some (⟨0, []⟩, []) ∧
    blockEnv false [] Data.core19.params ([], []) ((Data.core19.body.drop 0).take 96) = ([], []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwdsplit_19_96 : blockR (kwdlookJ 19) (kwdomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 96)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

end
end LeanVM.Guest
