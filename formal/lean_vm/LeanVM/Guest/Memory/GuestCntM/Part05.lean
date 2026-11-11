module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_350 : kwmStaticRange 350 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_357 : kwmStaticRange 357 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_387 : kwmStaticRange 387 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_417 : kwmStaticRange 417 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_447 : kwmStaticRange 447 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
