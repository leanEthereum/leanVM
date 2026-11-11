module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1343 : kvkStaticRange 1343 11 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1354 : kvkStaticRange 1354 19 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
