module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_653 : kvjStaticRange 653 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_670 : kvjStaticRange 670 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
