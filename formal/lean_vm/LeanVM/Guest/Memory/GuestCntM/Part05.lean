module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_320 : kwmStaticRange 320 2 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_322 : kwmStaticRange 322 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_352 : kwmStaticRange 352 30 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_382 : kwmStaticRange 382 30 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
