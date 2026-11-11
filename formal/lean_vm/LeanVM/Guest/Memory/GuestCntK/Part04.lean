module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_337 : kwkStaticRange 337 7 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_344 : kwkStaticRange 344 6 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
