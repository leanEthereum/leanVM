module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_307 : kwkStaticRange 307 7 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_314 : kwkStaticRange 314 7 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
