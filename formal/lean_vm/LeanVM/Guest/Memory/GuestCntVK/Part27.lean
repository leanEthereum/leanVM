module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_718 : kvkStaticRange 718 13 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_731 : kvkStaticRange 731 17 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
