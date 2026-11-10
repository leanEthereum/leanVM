module

public import LeanVM.Guest.Memory.GuestCntVX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvxstaticRange_848 : kvxStaticRange 848 15 := by
  unfold kvxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvxstaticRange_863 : kvxStaticRange 863 18 := by
  unfold kvxStaticRange; decide +kernel

end
end LeanVM.Guest
