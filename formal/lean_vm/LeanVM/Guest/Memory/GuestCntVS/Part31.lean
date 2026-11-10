module

public import LeanVM.Guest.Memory.GuestCntVS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvsstaticRange_848 : kvsStaticRange 848 15 := by
  unfold kvsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvsstaticRange_863 : kvsStaticRange 863 18 := by
  unfold kvsStaticRange; decide +kernel

end
end LeanVM.Guest
