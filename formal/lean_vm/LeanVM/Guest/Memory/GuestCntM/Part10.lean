module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_1516 : kwmStaticRange 1516 19 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
