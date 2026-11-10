module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1782 : kvkStaticRange 1782 11 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_1793 : kvkStaticRange 1793 10 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
