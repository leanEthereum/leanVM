module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_980 : kvjStaticRange 980 13 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_993 : kvjStaticRange 993 11 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1004 : kvjStaticRange 1004 12 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
