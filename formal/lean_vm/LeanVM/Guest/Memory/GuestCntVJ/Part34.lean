module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_987 : kvjStaticRange 987 15 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1002 : kvjStaticRange 1002 13 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
