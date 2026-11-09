module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_972 : kvjStaticRange 972 9 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_981 : kvjStaticRange 981 7 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_988 : kvjStaticRange 988 3 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
