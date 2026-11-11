module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_574 : kvjStaticRange 574 19 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_593 : kvjStaticRange 593 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
