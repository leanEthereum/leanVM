module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_321 : kwjStaticRange 321 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_328 : kwjStaticRange 328 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_358 : kwjStaticRange 358 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_388 : kwjStaticRange 388 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_418 : kwjStaticRange 418 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
