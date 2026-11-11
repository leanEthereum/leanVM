module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1700 : kvkStaticRange 1700 12 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1712 : kvkStaticRange 1712 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
