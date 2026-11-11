module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_1516 : kwkStaticRange 1516 19 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
