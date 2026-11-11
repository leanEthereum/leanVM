module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_808 : kvkStaticRange 808 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_821 : kvkStaticRange 821 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
