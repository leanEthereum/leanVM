module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_779 : kvsStaticRange 779 18 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_797 : kvsStaticRange 797 16 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
