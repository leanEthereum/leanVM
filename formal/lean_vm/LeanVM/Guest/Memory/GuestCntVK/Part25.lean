module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_730 : kvkStaticRange 730 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_748 : kvkStaticRange 748 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
