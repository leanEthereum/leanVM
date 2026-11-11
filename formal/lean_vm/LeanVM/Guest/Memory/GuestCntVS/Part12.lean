module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1645 : kvsStaticRange 1645 16 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1661 : kvsStaticRange 1661 13 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
