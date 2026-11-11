module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_337 : kwmStaticRange 337 7 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_344 : kwmStaticRange 344 6 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
