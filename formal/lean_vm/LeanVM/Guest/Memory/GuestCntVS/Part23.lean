module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_576 : kvsStaticRange 576 19 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_595 : kvsStaticRange 595 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
