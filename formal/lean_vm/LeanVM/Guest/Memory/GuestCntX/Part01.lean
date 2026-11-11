module

public import LeanVM.Guest.Memory.GuestCntX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwxsplit_19_96 : blockR (kwxlookJ 19) (kwxomLookJ 19) false [] Data.core19.params Data.core19.name (Data.core19.body.drop 96)
    ([], []) = some (⟨0, []⟩, []) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem kwxstaticRange_20 : kwxStaticRange 20 16 := by
  unfold kwxStaticRange; decide +kernel

end
end LeanVM.Guest
