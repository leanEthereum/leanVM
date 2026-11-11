module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1581 : kvsStaticRange 1581 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1593 : kvsStaticRange 1593 8 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
