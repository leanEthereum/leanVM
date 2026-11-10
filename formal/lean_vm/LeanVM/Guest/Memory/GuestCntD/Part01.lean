module

public import LeanVM.Guest.Memory.GuestCntD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

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

set_option maxRecDepth 100000 in
theorem kwdstaticRange_20 : kwdStaticRange 20 16 := by
  unfold kwdStaticRange; decide +kernel

end
end LeanVM.Guest
