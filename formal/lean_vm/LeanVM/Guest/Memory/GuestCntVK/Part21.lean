module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1452 : kvkStaticRange 1452 19 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1471 : kvkStaticRange 1471 12 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
