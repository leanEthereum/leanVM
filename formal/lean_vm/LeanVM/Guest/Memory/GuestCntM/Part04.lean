module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_337 : kwmStaticRange 337 3 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_340 : kwmStaticRange 340 3 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
