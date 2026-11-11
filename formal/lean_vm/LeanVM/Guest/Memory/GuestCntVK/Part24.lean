module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1530 : kvkStaticRange 1530 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1543 : kvkStaticRange 1543 13 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
