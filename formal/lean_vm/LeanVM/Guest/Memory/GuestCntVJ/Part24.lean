module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_694 : kvjStaticRange 694 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_712 : kvjStaticRange 712 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
