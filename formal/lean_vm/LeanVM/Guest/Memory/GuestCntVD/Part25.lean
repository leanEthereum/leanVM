module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_745 : kvdStaticRange 745 15 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_760 : kvdStaticRange 760 19 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
