module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_653 : kvkStaticRange 653 17 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_670 : kvkStaticRange 670 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
