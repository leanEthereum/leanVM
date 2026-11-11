module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1397 : kvkStaticRange 1397 18 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1415 : kvkStaticRange 1415 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
