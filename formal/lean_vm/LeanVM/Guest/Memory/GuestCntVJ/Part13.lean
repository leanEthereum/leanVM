module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1674 : kvjStaticRange 1674 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1687 : kvjStaticRange 1687 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
