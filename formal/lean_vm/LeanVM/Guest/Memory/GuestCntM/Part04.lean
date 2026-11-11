module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_336 : kwmStaticRange 336 6 := by
  unfold kwmStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwmstaticRange_342 : kwmStaticRange 342 6 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
