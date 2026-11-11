module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_778 : kvsStaticRange 778 12 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_790 : kvsStaticRange 790 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
