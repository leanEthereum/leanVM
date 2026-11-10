module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_649 : kvsStaticRange 649 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_666 : kvsStaticRange 666 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
