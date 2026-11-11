module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1433 : kvjStaticRange 1433 8 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1441 : kvjStaticRange 1441 11 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
