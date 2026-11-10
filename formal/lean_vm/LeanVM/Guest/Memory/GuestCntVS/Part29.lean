module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_779 : kvsStaticRange 779 19 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_798 : kvsStaticRange 798 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
