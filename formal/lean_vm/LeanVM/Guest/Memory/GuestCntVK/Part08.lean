module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1009 : kvkStaticRange 1009 20 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1029 : kvkStaticRange 1029 19 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1048 : kvkStaticRange 1048 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
