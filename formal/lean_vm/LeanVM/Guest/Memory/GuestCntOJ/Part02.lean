module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_15 : kwojStaticRange 15 2 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
