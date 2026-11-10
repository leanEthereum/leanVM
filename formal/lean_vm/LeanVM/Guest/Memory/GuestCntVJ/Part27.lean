module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_718 : kvjStaticRange 718 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_731 : kvjStaticRange 731 17 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
