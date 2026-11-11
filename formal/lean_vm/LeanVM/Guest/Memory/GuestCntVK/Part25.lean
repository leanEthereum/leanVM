module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_745 : kvkStaticRange 745 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_760 : kvkStaticRange 760 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
