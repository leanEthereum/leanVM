module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_748 : kvsStaticRange 748 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_765 : kvsStaticRange 765 14 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
