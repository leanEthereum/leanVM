module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_688 : kvkStaticRange 688 14 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_702 : kvkStaticRange 702 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
