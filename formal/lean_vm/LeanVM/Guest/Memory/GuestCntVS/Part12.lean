module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1479 : kvsStaticRange 1479 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1491 : kvsStaticRange 1491 12 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
