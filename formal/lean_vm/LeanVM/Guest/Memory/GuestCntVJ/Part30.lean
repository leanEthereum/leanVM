module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_954 : kvjStaticRange 954 12 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_966 : kvjStaticRange 966 14 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
