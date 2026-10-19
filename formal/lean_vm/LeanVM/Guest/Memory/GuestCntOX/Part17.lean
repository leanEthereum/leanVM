module

public import LeanVM.Guest.Memory.GuestCntOX.Range

namespace LeanVM.Guest

open Core Memory Data

@[expose] public section

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_634 : kwoxStaticRange 634 15 := by
  unfold kwoxStaticRange; decide +kernel

set_option maxRecDepth 100000 in
theorem kwoxstaticRange_649 : kwoxStaticRange 649 15 := by
  unfold kwoxStaticRange; decide +kernel

end
end LeanVM.Guest
