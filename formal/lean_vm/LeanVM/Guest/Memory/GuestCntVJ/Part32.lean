module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_939 : kvjStaticRange 939 15 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_954 : kvjStaticRange 954 14 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
