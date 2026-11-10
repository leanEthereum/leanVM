module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_688 : kvjStaticRange 688 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_702 : kvjStaticRange 702 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
