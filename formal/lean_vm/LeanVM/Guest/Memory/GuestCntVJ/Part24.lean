module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_712 : kvjStaticRange 712 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_729 : kvjStaticRange 729 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
