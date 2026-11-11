module

public import LeanVM.Guest.Memory.GuestCntK.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwkstaticRange_350 : kwkStaticRange 350 7 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_357 : kwkStaticRange 357 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_387 : kwkStaticRange 387 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_417 : kwkStaticRange 417 30 := by
  unfold kwkStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwkstaticRange_447 : kwkStaticRange 447 30 := by
  unfold kwkStaticRange; decide +kernel

end
end LeanVM.Guest
