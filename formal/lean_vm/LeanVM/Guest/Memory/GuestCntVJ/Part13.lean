module

public import LeanVM.Guest.Memory.GuestCntVJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1227 : kvjStaticRange 1227 19 := by
  unfold kvjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kvjstaticRange_1246 : kvjStaticRange 1246 11 := by
  unfold kvjStaticRange; decide +kernel

end
end LeanVM.Guest
