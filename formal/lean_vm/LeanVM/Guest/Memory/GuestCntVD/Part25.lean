module

public import LeanVM.Guest.Memory.GuestCntVD.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvdstaticRange_730 : kvdStaticRange 730 18 := by
  unfold kvdStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvdstaticRange_748 : kvdStaticRange 748 18 := by
  unfold kvdStaticRange; decide +kernel

end
end LeanVM.Guest
