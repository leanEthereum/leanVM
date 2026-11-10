module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1782 : kvjStaticRange 1782 11 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1793 : kvjStaticRange 1793 10 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
