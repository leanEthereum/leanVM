module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwssplit_19_96 : blockR (kwslookJ 19) (kwsomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 96)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_20 : kwsStaticRange 20 16 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
