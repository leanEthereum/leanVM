module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1759 : kvsStaticRange 1759 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1771 : kvsStaticRange 1771 11 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
