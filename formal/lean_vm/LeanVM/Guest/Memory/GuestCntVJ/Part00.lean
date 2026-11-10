module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_0 : kvjStaticRange 0 11 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_11 : kvjStaticRange 11 7 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
