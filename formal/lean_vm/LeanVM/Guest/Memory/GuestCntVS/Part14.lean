module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1700 : kvsStaticRange 1700 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1712 : kvsStaticRange 1712 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
