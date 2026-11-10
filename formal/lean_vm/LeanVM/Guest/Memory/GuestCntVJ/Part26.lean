module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_683 : kvjStaticRange 683 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_700 : kvjStaticRange 700 18 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
