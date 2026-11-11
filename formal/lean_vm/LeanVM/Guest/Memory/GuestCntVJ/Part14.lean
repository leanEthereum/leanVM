module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1257 : kvjStaticRange 1257 14 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1271 : kvjStaticRange 1271 21 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
