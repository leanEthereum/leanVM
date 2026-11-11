module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_712 : kvkStaticRange 712 17 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_729 : kvkStaticRange 729 13 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
