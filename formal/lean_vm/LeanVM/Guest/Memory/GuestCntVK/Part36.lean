module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1048 : kvkStaticRange 1048 7 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
