module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1653 : kvkStaticRange 1653 21 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1674 : kvkStaticRange 1674 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1692 : kvkStaticRange 1692 15 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
