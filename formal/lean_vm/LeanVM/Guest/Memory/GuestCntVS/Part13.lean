module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1674 : kvsStaticRange 1674 13 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_1687 : kvsStaticRange 1687 13 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
