module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1645 : kvjStaticRange 1645 16 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1661 : kvjStaticRange 1661 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
