module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_779 : kvjStaticRange 779 19 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_798 : kvjStaticRange 798 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
