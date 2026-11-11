module

public import LeanVM.Guest.Memory.GuestCntS.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwsstaticRange_350 : kwsStaticRange 350 7 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_357 : kwsStaticRange 357 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_387 : kwsStaticRange 387 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_417 : kwsStaticRange 417 30 := by
  unfold kwsStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwsstaticRange_447 : kwsStaticRange 447 30 := by
  unfold kwsStaticRange; decide +kernel

end
end LeanVM.Guest
