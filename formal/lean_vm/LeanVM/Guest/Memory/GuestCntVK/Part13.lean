module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1707 : kvkStaticRange 1707 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1720 : kvkStaticRange 1720 15 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
