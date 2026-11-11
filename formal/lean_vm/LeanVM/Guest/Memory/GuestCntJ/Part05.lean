module

public import LeanVM.Guest.Memory.GuestCntJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwjstaticRange_350 : kwjStaticRange 350 7 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_357 : kwjStaticRange 357 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_387 : kwjStaticRange 387 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_417 : kwjStaticRange 417 30 := by
  unfold kwjStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwjstaticRange_447 : kwjStaticRange 447 30 := by
  unfold kwjStaticRange; decide +kernel

end
end LeanVM.Guest
