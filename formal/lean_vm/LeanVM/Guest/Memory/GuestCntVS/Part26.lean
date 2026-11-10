module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_688 : kvsStaticRange 688 14 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_702 : kvsStaticRange 702 19 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
