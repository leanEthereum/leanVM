module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1581 : kvdStaticRange 1581 12 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1593 : kvdStaticRange 1593 8 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
