module

public import LeanVM.Guest.Memory.GuestCntVM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvmstaticRange_930 : kvmStaticRange 930 17 := by
  unfold kvmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvmstaticRange_947 : kvmStaticRange 947 12 := by
  unfold kvmStaticRange; decide +kernel

end
end LeanVM.Guest
