module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1645 : kvkStaticRange 1645 16 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1661 : kvkStaticRange 1661 13 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
