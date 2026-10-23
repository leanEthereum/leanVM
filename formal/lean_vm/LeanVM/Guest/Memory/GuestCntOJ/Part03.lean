module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_17 : kwojStaticRange 17 1 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
