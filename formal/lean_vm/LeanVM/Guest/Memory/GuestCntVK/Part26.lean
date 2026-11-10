module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_683 : kvkStaticRange 683 17 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_700 : kvkStaticRange 700 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
