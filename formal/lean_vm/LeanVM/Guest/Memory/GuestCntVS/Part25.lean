module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1556 : kvsStaticRange 1556 13 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1569 : kvsStaticRange 1569 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
