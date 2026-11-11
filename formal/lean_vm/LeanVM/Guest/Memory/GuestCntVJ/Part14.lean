module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1525 : kvjStaticRange 1525 10 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
