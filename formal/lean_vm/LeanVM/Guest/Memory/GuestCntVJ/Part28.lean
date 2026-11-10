module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_748 : kvjStaticRange 748 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_765 : kvjStaticRange 765 14 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
