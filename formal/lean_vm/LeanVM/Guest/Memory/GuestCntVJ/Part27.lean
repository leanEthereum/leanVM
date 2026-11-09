module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_850 : kvjStaticRange 850 17 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_867 : kvjStaticRange 867 16 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
