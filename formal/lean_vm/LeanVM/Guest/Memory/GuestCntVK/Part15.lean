module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1292 : kvkStaticRange 1292 8 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1300 : kvkStaticRange 1300 11 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
