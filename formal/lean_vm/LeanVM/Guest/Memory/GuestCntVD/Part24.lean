module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1530 : kvdStaticRange 1530 13 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_1543 : kvdStaticRange 1543 13 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
