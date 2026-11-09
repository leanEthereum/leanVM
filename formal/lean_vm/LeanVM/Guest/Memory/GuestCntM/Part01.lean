module

public import LeanVM.Guest.Memory.GuestCntM.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwmstaticRange_20 : kwmStaticRange 20 16 := by
  unfold kwmStaticRange; decide +kernel

end
end LeanVM.Guest
