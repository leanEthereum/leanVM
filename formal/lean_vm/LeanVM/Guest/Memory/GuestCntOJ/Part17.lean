module

public import LeanVM.Guest.Memory.GuestCntOJ.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwojstaticRange_634 : kwojStaticRange 634 15 := by
  unfold kwojStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwojstaticRange_649 : kwojStaticRange 649 15 := by
  unfold kwojStaticRange; decide +kernel

end
end LeanVM.Guest
