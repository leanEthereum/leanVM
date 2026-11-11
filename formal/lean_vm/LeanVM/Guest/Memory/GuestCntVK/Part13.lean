module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1674 : kvkStaticRange 1674 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1687 : kvkStaticRange 1687 13 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
