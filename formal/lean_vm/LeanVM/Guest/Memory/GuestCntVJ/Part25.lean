module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_730 : kvjStaticRange 730 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_748 : kvjStaticRange 748 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
