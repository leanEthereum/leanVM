module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_20 : kwkStaticRange 20 16 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
