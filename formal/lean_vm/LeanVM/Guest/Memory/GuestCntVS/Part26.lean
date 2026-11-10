module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_683 : kvsStaticRange 683 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_700 : kvsStaticRange 700 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
