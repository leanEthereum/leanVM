module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_930 : kvdStaticRange 930 17 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_947 : kvdStaticRange 947 12 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
