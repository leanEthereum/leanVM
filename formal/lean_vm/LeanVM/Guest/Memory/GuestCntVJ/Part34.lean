module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_991 : kvjStaticRange 991 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1005 : kvjStaticRange 1005 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
