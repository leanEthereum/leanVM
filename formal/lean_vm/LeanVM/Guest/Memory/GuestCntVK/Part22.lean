module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1483 : kvkStaticRange 1483 8 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1491 : kvkStaticRange 1491 11 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
