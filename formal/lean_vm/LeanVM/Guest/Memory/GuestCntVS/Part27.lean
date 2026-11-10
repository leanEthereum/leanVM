module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_721 : kvsStaticRange 721 17 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_738 : kvsStaticRange 738 17 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
