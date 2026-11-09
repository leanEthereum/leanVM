module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_661 : kvjStaticRange 661 18 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_679 : kvjStaticRange 679 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
