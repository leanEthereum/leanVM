module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_883 : kvjStaticRange 883 15 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_898 : kvjStaticRange 898 15 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
