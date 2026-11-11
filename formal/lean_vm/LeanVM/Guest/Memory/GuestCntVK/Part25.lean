module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1556 : kvkStaticRange 1556 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1569 : kvkStaticRange 1569 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
