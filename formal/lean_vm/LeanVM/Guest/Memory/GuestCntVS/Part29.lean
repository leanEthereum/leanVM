module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_930 : kvsStaticRange 930 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_947 : kvsStaticRange 947 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
