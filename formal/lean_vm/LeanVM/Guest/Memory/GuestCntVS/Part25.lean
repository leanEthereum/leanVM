module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_742 : kvsStaticRange 742 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_759 : kvsStaticRange 759 19 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
