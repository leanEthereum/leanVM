module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_848 : kvdStaticRange 848 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_863 : kvdStaticRange 863 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
