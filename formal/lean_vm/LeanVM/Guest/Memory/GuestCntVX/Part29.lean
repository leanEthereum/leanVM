module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_930 : kvxStaticRange 930 17 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_947 : kvxStaticRange 947 12 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
