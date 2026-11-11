module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_742 : kvjStaticRange 742 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_759 : kvjStaticRange 759 19 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
