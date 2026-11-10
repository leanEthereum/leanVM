module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_336 : kwkStaticRange 336 6 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_342 : kwkStaticRange 342 6 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
