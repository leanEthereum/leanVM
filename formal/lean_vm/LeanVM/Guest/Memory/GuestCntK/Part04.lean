module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_313 : kwkStaticRange 313 3 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_316 : kwkStaticRange 316 3 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
