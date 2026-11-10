module

public import LeanVM.Guest.Memory.GuestCntVK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvkstaticRange_848 : kvkStaticRange 848 15 := by
  unfold kvkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvkstaticRange_863 : kvkStaticRange 863 18 := by
  unfold kvkStaticRange; decide +kernel

end
end LeanVM.Guest
